%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:26 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   39 (  54 expanded)
%              Number of leaves         :   17 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   50 (  84 expanded)
%              Number of equality atoms :   16 (  39 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > #nlpp > k2_relat_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k1_subset_1,type,(
    k1_subset_1: $i > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ( k1_relat_1(A) = k1_xboole_0
            | k2_relat_1(A) = k1_xboole_0 )
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_31,axiom,(
    ! [A] : k1_subset_1(A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_subset_1)).

tff(f_33,axiom,(
    ! [A] : v1_xboole_0(k1_subset_1(A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc13_subset_1)).

tff(f_45,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_boole)).

tff(f_53,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_37,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(c_14,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_18,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_4,plain,(
    ! [A_2] : k1_subset_1(A_2) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_3] : v1_xboole_0(k1_subset_1(A_3)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_19,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_16,plain,
    ( k2_relat_1('#skF_1') = k1_xboole_0
    | k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_56,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_95,plain,(
    ! [A_12] :
      ( ~ v1_xboole_0(k1_relat_1(A_12))
      | ~ v1_relat_1(A_12)
      | v1_xboole_0(A_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_101,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_95])).

tff(c_111,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_19,c_101])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_120,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_111,c_2])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_120])).

tff(c_128,plain,(
    k1_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_127,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_133,plain,(
    ! [A_13] :
      ( ~ v1_xboole_0(k2_relat_1(A_13))
      | ~ v1_relat_1(A_13)
      | v1_xboole_0(A_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_136,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_133])).

tff(c_138,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_19,c_136])).

tff(c_33,plain,(
    ! [A_9] :
      ( v1_xboole_0(k1_relat_1(A_9))
      | ~ v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_37,plain,(
    ! [A_9] :
      ( k1_relat_1(A_9) = k1_xboole_0
      | ~ v1_xboole_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_33,c_2])).

tff(c_141,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_138,c_37])).

tff(c_148,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_128,c_141])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n002.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:59:06 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.19  
% 1.82/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.19  %$ v1_xboole_0 > v1_relat_1 > #nlpp > k2_relat_1 > k1_subset_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.82/1.19  
% 1.82/1.19  %Foreground sorts:
% 1.82/1.19  
% 1.82/1.19  
% 1.82/1.19  %Background operators:
% 1.82/1.19  
% 1.82/1.19  
% 1.82/1.19  %Foreground operators:
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.19  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.82/1.19  tff('#skF_1', type, '#skF_1': $i).
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.19  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.82/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.19  tff(k1_subset_1, type, k1_subset_1: $i > $i).
% 1.82/1.19  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.82/1.19  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.82/1.19  
% 1.82/1.20  tff(f_62, negated_conjecture, ~(![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 1.82/1.20  tff(f_31, axiom, (![A]: (k1_subset_1(A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_subset_1)).
% 1.82/1.20  tff(f_33, axiom, (![A]: v1_xboole_0(k1_subset_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc13_subset_1)).
% 1.82/1.20  tff(f_45, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 1.82/1.20  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_boole)).
% 1.82/1.20  tff(f_53, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 1.82/1.20  tff(f_37, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 1.82/1.20  tff(c_14, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.82/1.20  tff(c_18, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.82/1.20  tff(c_4, plain, (![A_2]: (k1_subset_1(A_2)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.82/1.20  tff(c_6, plain, (![A_3]: (v1_xboole_0(k1_subset_1(A_3)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.82/1.20  tff(c_19, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 1.82/1.20  tff(c_16, plain, (k2_relat_1('#skF_1')=k1_xboole_0 | k1_relat_1('#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.82/1.20  tff(c_56, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_16])).
% 1.82/1.20  tff(c_95, plain, (![A_12]: (~v1_xboole_0(k1_relat_1(A_12)) | ~v1_relat_1(A_12) | v1_xboole_0(A_12))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.82/1.20  tff(c_101, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_56, c_95])).
% 1.82/1.20  tff(c_111, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_19, c_101])).
% 1.82/1.20  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.82/1.20  tff(c_120, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_111, c_2])).
% 1.82/1.20  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_120])).
% 1.82/1.20  tff(c_128, plain, (k1_relat_1('#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_16])).
% 1.82/1.20  tff(c_127, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_16])).
% 1.82/1.20  tff(c_133, plain, (![A_13]: (~v1_xboole_0(k2_relat_1(A_13)) | ~v1_relat_1(A_13) | v1_xboole_0(A_13))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.82/1.20  tff(c_136, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_127, c_133])).
% 1.82/1.20  tff(c_138, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_19, c_136])).
% 1.82/1.20  tff(c_33, plain, (![A_9]: (v1_xboole_0(k1_relat_1(A_9)) | ~v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.82/1.20  tff(c_37, plain, (![A_9]: (k1_relat_1(A_9)=k1_xboole_0 | ~v1_xboole_0(A_9))), inference(resolution, [status(thm)], [c_33, c_2])).
% 1.82/1.20  tff(c_141, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(resolution, [status(thm)], [c_138, c_37])).
% 1.82/1.20  tff(c_148, plain, $false, inference(negUnitSimplification, [status(thm)], [c_128, c_141])).
% 1.82/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.20  
% 1.82/1.20  Inference rules
% 1.82/1.20  ----------------------
% 1.82/1.20  #Ref     : 0
% 1.82/1.20  #Sup     : 30
% 1.82/1.20  #Fact    : 0
% 1.82/1.20  #Define  : 0
% 1.82/1.20  #Split   : 1
% 1.82/1.20  #Chain   : 0
% 1.82/1.20  #Close   : 0
% 1.82/1.20  
% 1.82/1.20  Ordering : KBO
% 1.82/1.20  
% 1.82/1.20  Simplification rules
% 1.82/1.20  ----------------------
% 1.82/1.20  #Subsume      : 1
% 1.82/1.20  #Demod        : 18
% 1.82/1.20  #Tautology    : 21
% 1.82/1.20  #SimpNegUnit  : 2
% 1.82/1.20  #BackRed      : 0
% 1.82/1.20  
% 1.82/1.20  #Partial instantiations: 0
% 1.82/1.20  #Strategies tried      : 1
% 1.82/1.20  
% 1.82/1.20  Timing (in seconds)
% 1.82/1.20  ----------------------
% 1.82/1.20  Preprocessing        : 0.29
% 1.82/1.20  Parsing              : 0.16
% 1.82/1.20  CNF conversion       : 0.02
% 1.82/1.20  Main loop            : 0.12
% 1.82/1.20  Inferencing          : 0.04
% 1.82/1.20  Reduction            : 0.04
% 1.82/1.20  Demodulation         : 0.03
% 1.82/1.20  BG Simplification    : 0.01
% 1.82/1.20  Subsumption          : 0.02
% 1.82/1.20  Abstraction          : 0.01
% 1.82/1.20  MUC search           : 0.00
% 1.82/1.20  Cooper               : 0.00
% 1.82/1.20  Total                : 0.43
% 1.82/1.20  Index Insertion      : 0.00
% 1.82/1.20  Index Deletion       : 0.00
% 1.82/1.20  Index Matching       : 0.00
% 1.82/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

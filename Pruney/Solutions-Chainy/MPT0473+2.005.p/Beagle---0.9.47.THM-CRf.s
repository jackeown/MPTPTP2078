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
% DateTime   : Thu Dec  3 09:59:27 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   32 (  87 expanded)
%              Number of leaves         :   11 (  33 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 ( 162 expanded)
%              Number of equality atoms :   31 ( 125 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_43,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k1_relat_1(A) = k1_xboole_0
        <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_36,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_28,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(c_12,plain,
    ( k2_relat_1('#skF_1') != k1_xboole_0
    | k1_relat_1('#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_27,plain,(
    k1_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_12])).

tff(c_18,plain,
    ( k1_relat_1('#skF_1') = k1_xboole_0
    | k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_28,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_27,c_18])).

tff(c_10,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_33,plain,(
    ! [A_2] :
      ( k2_relat_1(A_2) != k1_xboole_0
      | k1_xboole_0 = A_2
      | ~ v1_relat_1(A_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_36,plain,
    ( k2_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10,c_33])).

tff(c_39,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_36])).

tff(c_42,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_27])).

tff(c_4,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_43,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_39,c_4])).

tff(c_54,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_43])).

tff(c_56,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_63,plain,(
    ! [A_3] :
      ( k1_relat_1(A_3) != k1_xboole_0
      | k1_xboole_0 = A_3
      | ~ v1_relat_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,
    ( k1_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_10,c_63])).

tff(c_69,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_66])).

tff(c_55,plain,(
    k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_12])).

tff(c_72,plain,(
    k2_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_55])).

tff(c_2,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_74,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_69,c_69,c_2])).

tff(c_90,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_74])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:02 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.09  
% 1.63/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.09  %$ v1_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.63/1.09  
% 1.63/1.09  %Foreground sorts:
% 1.63/1.09  
% 1.63/1.09  
% 1.63/1.09  %Background operators:
% 1.63/1.09  
% 1.63/1.09  
% 1.63/1.09  %Foreground operators:
% 1.63/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.09  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.63/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.09  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.63/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.09  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.63/1.09  
% 1.63/1.10  tff(f_43, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_relat_1)).
% 1.63/1.10  tff(f_36, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_relat_1)).
% 1.63/1.10  tff(f_28, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.63/1.10  tff(c_12, plain, (k2_relat_1('#skF_1')!=k1_xboole_0 | k1_relat_1('#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.63/1.10  tff(c_27, plain, (k1_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_12])).
% 1.63/1.10  tff(c_18, plain, (k1_relat_1('#skF_1')=k1_xboole_0 | k2_relat_1('#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.63/1.10  tff(c_28, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_27, c_18])).
% 1.63/1.10  tff(c_10, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.63/1.10  tff(c_33, plain, (![A_2]: (k2_relat_1(A_2)!=k1_xboole_0 | k1_xboole_0=A_2 | ~v1_relat_1(A_2))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.63/1.10  tff(c_36, plain, (k2_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_10, c_33])).
% 1.63/1.10  tff(c_39, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_28, c_36])).
% 1.63/1.10  tff(c_42, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_39, c_27])).
% 1.63/1.10  tff(c_4, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.63/1.10  tff(c_43, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_39, c_39, c_4])).
% 1.63/1.10  tff(c_54, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_43])).
% 1.63/1.10  tff(c_56, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_12])).
% 1.63/1.10  tff(c_63, plain, (![A_3]: (k1_relat_1(A_3)!=k1_xboole_0 | k1_xboole_0=A_3 | ~v1_relat_1(A_3))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.63/1.10  tff(c_66, plain, (k1_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_10, c_63])).
% 1.63/1.10  tff(c_69, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_66])).
% 1.63/1.10  tff(c_55, plain, (k2_relat_1('#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_12])).
% 1.63/1.10  tff(c_72, plain, (k2_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_55])).
% 1.63/1.10  tff(c_2, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.63/1.10  tff(c_74, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_69, c_69, c_2])).
% 1.63/1.10  tff(c_90, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_74])).
% 1.63/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.10  
% 1.63/1.10  Inference rules
% 1.63/1.10  ----------------------
% 1.63/1.10  #Ref     : 0
% 1.63/1.10  #Sup     : 19
% 1.63/1.10  #Fact    : 0
% 1.63/1.10  #Define  : 0
% 1.63/1.10  #Split   : 1
% 1.63/1.10  #Chain   : 0
% 1.63/1.10  #Close   : 0
% 1.63/1.10  
% 1.63/1.10  Ordering : KBO
% 1.63/1.10  
% 1.63/1.10  Simplification rules
% 1.63/1.10  ----------------------
% 1.63/1.10  #Subsume      : 1
% 1.63/1.10  #Demod        : 23
% 1.63/1.10  #Tautology    : 21
% 1.63/1.10  #SimpNegUnit  : 4
% 1.63/1.10  #BackRed      : 10
% 1.63/1.10  
% 1.63/1.10  #Partial instantiations: 0
% 1.63/1.10  #Strategies tried      : 1
% 1.63/1.10  
% 1.63/1.10  Timing (in seconds)
% 1.63/1.10  ----------------------
% 1.63/1.10  Preprocessing        : 0.24
% 1.63/1.10  Parsing              : 0.14
% 1.63/1.10  CNF conversion       : 0.01
% 1.63/1.11  Main loop            : 0.10
% 1.63/1.11  Inferencing          : 0.04
% 1.63/1.11  Reduction            : 0.03
% 1.63/1.11  Demodulation         : 0.02
% 1.63/1.11  BG Simplification    : 0.01
% 1.63/1.11  Subsumption          : 0.02
% 1.63/1.11  Abstraction          : 0.00
% 1.63/1.11  MUC search           : 0.00
% 1.63/1.11  Cooper               : 0.00
% 1.63/1.11  Total                : 0.37
% 1.63/1.11  Index Insertion      : 0.00
% 1.63/1.11  Index Deletion       : 0.00
% 1.63/1.11  Index Matching       : 0.00
% 1.63/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------

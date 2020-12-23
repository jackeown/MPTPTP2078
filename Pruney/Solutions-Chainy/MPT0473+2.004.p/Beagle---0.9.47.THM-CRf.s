%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:27 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.68s
% Verified   : 
% Statistics : Number of formulae       :   49 ( 124 expanded)
%              Number of leaves         :   16 (  49 expanded)
%              Depth                    :    9
%              Number of atoms          :   62 ( 178 expanded)
%              Number of equality atoms :   31 (  89 expanded)
%              Maximal formula depth    :    5 (   2 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_xboole_0 > v1_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

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

tff(f_31,axiom,(
    ? [A] : v1_xboole_0(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',rc1_xboole_0)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_50,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_57,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k1_relat_1(A) = k1_xboole_0
        <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_31,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_35,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_31])).

tff(c_10,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_98,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_35,c_10])).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_39,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_35,c_12])).

tff(c_16,plain,
    ( k2_relat_1('#skF_2') != k1_xboole_0
    | k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36,plain,(
    k1_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_44,plain,(
    k1_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_36])).

tff(c_22,plain,
    ( k1_relat_1('#skF_2') = k1_xboole_0
    | k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_49,plain,
    ( k1_relat_1('#skF_2') = '#skF_1'
    | k2_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_35,c_22])).

tff(c_50,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_49])).

tff(c_71,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(k2_relat_1(A_7))
      | ~ v1_relat_1(A_7)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_77,plain,
    ( ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_71])).

tff(c_81,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_4,c_77])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_37,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_2])).

tff(c_85,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_81,c_37])).

tff(c_88,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_44])).

tff(c_94,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_88])).

tff(c_96,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_105,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_96])).

tff(c_126,plain,(
    ! [A_9] :
      ( ~ v1_xboole_0(k1_relat_1(A_9))
      | ~ v1_relat_1(A_9)
      | v1_xboole_0(A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_132,plain,
    ( ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_126])).

tff(c_136,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_4,c_132])).

tff(c_97,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_2])).

tff(c_140,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_136,c_97])).

tff(c_95,plain,(
    k2_relat_1('#skF_2') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_104,plain,(
    k2_relat_1('#skF_2') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_35,c_95])).

tff(c_149,plain,(
    k2_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_104])).

tff(c_155,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_98,c_149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:59:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.13  
% 1.68/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.13  %$ v1_xboole_0 > v1_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.68/1.13  
% 1.68/1.13  %Foreground sorts:
% 1.68/1.13  
% 1.68/1.13  
% 1.68/1.13  %Background operators:
% 1.68/1.13  
% 1.68/1.13  
% 1.68/1.13  %Foreground operators:
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.68/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.68/1.13  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.68/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.68/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.68/1.13  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.68/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.68/1.13  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.68/1.13  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.68/1.13  
% 1.68/1.15  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.68/1.15  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.68/1.15  tff(f_50, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.68/1.15  tff(f_57, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 1.68/1.15  tff(f_47, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 1.68/1.15  tff(f_39, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 1.68/1.15  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.68/1.15  tff(c_31, plain, (![A_4]: (k1_xboole_0=A_4 | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.15  tff(c_35, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_31])).
% 1.68/1.15  tff(c_10, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.68/1.15  tff(c_98, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_35, c_35, c_10])).
% 1.68/1.15  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.68/1.15  tff(c_12, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.68/1.15  tff(c_39, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_35, c_35, c_12])).
% 1.68/1.15  tff(c_16, plain, (k2_relat_1('#skF_2')!=k1_xboole_0 | k1_relat_1('#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.68/1.15  tff(c_36, plain, (k1_relat_1('#skF_2')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_16])).
% 1.68/1.15  tff(c_44, plain, (k1_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_35, c_36])).
% 1.68/1.15  tff(c_22, plain, (k1_relat_1('#skF_2')=k1_xboole_0 | k2_relat_1('#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.68/1.15  tff(c_49, plain, (k1_relat_1('#skF_2')='#skF_1' | k2_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_35, c_35, c_22])).
% 1.68/1.15  tff(c_50, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(negUnitSimplification, [status(thm)], [c_44, c_49])).
% 1.68/1.15  tff(c_71, plain, (![A_7]: (~v1_xboole_0(k2_relat_1(A_7)) | ~v1_relat_1(A_7) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.68/1.15  tff(c_77, plain, (~v1_xboole_0('#skF_1') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_50, c_71])).
% 1.68/1.15  tff(c_81, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_4, c_77])).
% 1.68/1.15  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.68/1.15  tff(c_37, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_2])).
% 1.68/1.15  tff(c_85, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_81, c_37])).
% 1.68/1.15  tff(c_88, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_44])).
% 1.68/1.15  tff(c_94, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_39, c_88])).
% 1.68/1.15  tff(c_96, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(splitRight, [status(thm)], [c_16])).
% 1.68/1.15  tff(c_105, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_35, c_96])).
% 1.68/1.15  tff(c_126, plain, (![A_9]: (~v1_xboole_0(k1_relat_1(A_9)) | ~v1_relat_1(A_9) | v1_xboole_0(A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.68/1.15  tff(c_132, plain, (~v1_xboole_0('#skF_1') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_105, c_126])).
% 1.68/1.15  tff(c_136, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_4, c_132])).
% 1.68/1.15  tff(c_97, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_35, c_2])).
% 1.68/1.15  tff(c_140, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_136, c_97])).
% 1.68/1.15  tff(c_95, plain, (k2_relat_1('#skF_2')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_16])).
% 1.68/1.15  tff(c_104, plain, (k2_relat_1('#skF_2')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_35, c_95])).
% 1.68/1.15  tff(c_149, plain, (k2_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_140, c_104])).
% 1.68/1.15  tff(c_155, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_98, c_149])).
% 1.68/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.68/1.15  
% 1.68/1.15  Inference rules
% 1.68/1.15  ----------------------
% 1.68/1.15  #Ref     : 0
% 1.68/1.15  #Sup     : 31
% 1.68/1.15  #Fact    : 0
% 1.68/1.15  #Define  : 0
% 1.68/1.15  #Split   : 1
% 1.68/1.15  #Chain   : 0
% 1.68/1.15  #Close   : 0
% 1.68/1.15  
% 1.68/1.15  Ordering : KBO
% 1.68/1.15  
% 1.68/1.15  Simplification rules
% 1.68/1.15  ----------------------
% 1.68/1.15  #Subsume      : 0
% 1.68/1.15  #Demod        : 44
% 1.68/1.15  #Tautology    : 33
% 1.68/1.15  #SimpNegUnit  : 2
% 1.68/1.15  #BackRed      : 14
% 1.68/1.15  
% 1.68/1.15  #Partial instantiations: 0
% 1.68/1.15  #Strategies tried      : 1
% 1.68/1.15  
% 1.68/1.15  Timing (in seconds)
% 1.68/1.15  ----------------------
% 1.68/1.15  Preprocessing        : 0.27
% 1.68/1.15  Parsing              : 0.15
% 1.68/1.15  CNF conversion       : 0.02
% 1.68/1.15  Main loop            : 0.14
% 1.68/1.15  Inferencing          : 0.05
% 1.68/1.15  Reduction            : 0.04
% 1.68/1.15  Demodulation         : 0.03
% 1.68/1.15  BG Simplification    : 0.01
% 1.68/1.15  Subsumption          : 0.02
% 1.68/1.15  Abstraction          : 0.01
% 1.68/1.15  MUC search           : 0.00
% 1.68/1.15  Cooper               : 0.00
% 1.68/1.15  Total                : 0.44
% 1.68/1.15  Index Insertion      : 0.00
% 1.68/1.15  Index Deletion       : 0.00
% 1.68/1.15  Index Matching       : 0.00
% 1.68/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

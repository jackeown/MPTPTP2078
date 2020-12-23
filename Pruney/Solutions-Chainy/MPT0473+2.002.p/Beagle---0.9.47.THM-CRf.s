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
% DateTime   : Thu Dec  3 09:59:27 EST 2020

% Result     : Theorem 2.02s
% Output     : CNFRefutation 2.02s
% Verified   : 
% Statistics : Number of formulae       :   42 ( 100 expanded)
%              Number of leaves         :   15 (  38 expanded)
%              Depth                    :    6
%              Number of atoms          :   54 ( 182 expanded)
%              Number of equality atoms :   33 ( 127 expanded)
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

tff(f_53,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( k1_relat_1(A) = k1_xboole_0
        <=> k2_relat_1(A) = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_relat_1)).

tff(f_46,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => ( ( k1_relat_1(A) = k1_xboole_0
          | k2_relat_1(A) = k1_xboole_0 )
       => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_34,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc10_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc11_relat_1)).

tff(c_16,plain,
    ( k2_relat_1('#skF_1') != k1_xboole_0
    | k1_relat_1('#skF_1') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_39,plain,(
    k1_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_22,plain,
    ( k1_relat_1('#skF_1') = k1_xboole_0
    | k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_62,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_39,c_22])).

tff(c_14,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_218,plain,(
    ! [A_15] :
      ( k2_relat_1(A_15) != k1_xboole_0
      | k1_xboole_0 = A_15
      | ~ v1_relat_1(A_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_221,plain,
    ( k2_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_14,c_218])).

tff(c_224,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_62,c_221])).

tff(c_236,plain,(
    k1_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_39])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_29,plain,(
    ! [A_6] :
      ( v1_xboole_0(k1_relat_1(A_6))
      | ~ v1_xboole_0(A_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_71,plain,(
    ! [A_9] :
      ( k1_relat_1(A_9) = k1_xboole_0
      | ~ v1_xboole_0(A_9) ) ),
    inference(resolution,[status(thm)],[c_29,c_4])).

tff(c_83,plain,(
    k1_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_71])).

tff(c_231,plain,(
    k1_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_224,c_224,c_83])).

tff(c_250,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_236,c_231])).

tff(c_252,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_432,plain,(
    ! [A_23] :
      ( k1_relat_1(A_23) != k1_xboole_0
      | k1_xboole_0 = A_23
      | ~ v1_relat_1(A_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_435,plain,
    ( k1_relat_1('#skF_1') != k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_14,c_432])).

tff(c_438,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_252,c_435])).

tff(c_251,plain,(
    k2_relat_1('#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_450,plain,(
    k2_relat_1('#skF_1') != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_251])).

tff(c_34,plain,(
    ! [A_7] :
      ( v1_xboole_0(k2_relat_1(A_7))
      | ~ v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_263,plain,(
    ! [A_16] :
      ( k2_relat_1(A_16) = k1_xboole_0
      | ~ v1_xboole_0(A_16) ) ),
    inference(resolution,[status(thm)],[c_34,c_4])).

tff(c_275,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_2,c_263])).

tff(c_447,plain,(
    k2_relat_1('#skF_1') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_438,c_275])).

tff(c_466,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_450,c_447])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:40:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.02/1.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.22  
% 2.02/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.22  %$ v1_xboole_0 > v1_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 2.02/1.22  
% 2.02/1.22  %Foreground sorts:
% 2.02/1.22  
% 2.02/1.22  
% 2.02/1.22  %Background operators:
% 2.02/1.22  
% 2.02/1.22  
% 2.02/1.22  %Foreground operators:
% 2.02/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.02/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.02/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 2.02/1.22  tff('#skF_1', type, '#skF_1': $i).
% 2.02/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.02/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 2.02/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.02/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.02/1.22  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 2.02/1.22  
% 2.02/1.23  tff(f_53, negated_conjecture, ~(![A]: (v1_relat_1(A) => ((k1_relat_1(A) = k1_xboole_0) <=> (k2_relat_1(A) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_relat_1)).
% 2.02/1.23  tff(f_46, axiom, (![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 2.02/1.23  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.02/1.23  tff(f_34, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc10_relat_1)).
% 2.02/1.23  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.02/1.23  tff(f_38, axiom, (![A]: (v1_xboole_0(A) => v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc11_relat_1)).
% 2.02/1.23  tff(c_16, plain, (k2_relat_1('#skF_1')!=k1_xboole_0 | k1_relat_1('#skF_1')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.02/1.23  tff(c_39, plain, (k1_relat_1('#skF_1')!=k1_xboole_0), inference(splitLeft, [status(thm)], [c_16])).
% 2.02/1.23  tff(c_22, plain, (k1_relat_1('#skF_1')=k1_xboole_0 | k2_relat_1('#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.02/1.23  tff(c_62, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_39, c_22])).
% 2.02/1.23  tff(c_14, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.02/1.23  tff(c_218, plain, (![A_15]: (k2_relat_1(A_15)!=k1_xboole_0 | k1_xboole_0=A_15 | ~v1_relat_1(A_15))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.02/1.23  tff(c_221, plain, (k2_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_14, c_218])).
% 2.02/1.23  tff(c_224, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_62, c_221])).
% 2.02/1.23  tff(c_236, plain, (k1_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_224, c_39])).
% 2.02/1.23  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 2.02/1.23  tff(c_29, plain, (![A_6]: (v1_xboole_0(k1_relat_1(A_6)) | ~v1_xboole_0(A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.02/1.23  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 2.02/1.23  tff(c_71, plain, (![A_9]: (k1_relat_1(A_9)=k1_xboole_0 | ~v1_xboole_0(A_9))), inference(resolution, [status(thm)], [c_29, c_4])).
% 2.02/1.23  tff(c_83, plain, (k1_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_71])).
% 2.02/1.23  tff(c_231, plain, (k1_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_224, c_224, c_83])).
% 2.02/1.23  tff(c_250, plain, $false, inference(negUnitSimplification, [status(thm)], [c_236, c_231])).
% 2.02/1.23  tff(c_252, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(splitRight, [status(thm)], [c_16])).
% 2.02/1.23  tff(c_432, plain, (![A_23]: (k1_relat_1(A_23)!=k1_xboole_0 | k1_xboole_0=A_23 | ~v1_relat_1(A_23))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.02/1.23  tff(c_435, plain, (k1_relat_1('#skF_1')!=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_14, c_432])).
% 2.02/1.23  tff(c_438, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_252, c_435])).
% 2.02/1.23  tff(c_251, plain, (k2_relat_1('#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_16])).
% 2.02/1.23  tff(c_450, plain, (k2_relat_1('#skF_1')!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_438, c_251])).
% 2.02/1.23  tff(c_34, plain, (![A_7]: (v1_xboole_0(k2_relat_1(A_7)) | ~v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.02/1.23  tff(c_263, plain, (![A_16]: (k2_relat_1(A_16)=k1_xboole_0 | ~v1_xboole_0(A_16))), inference(resolution, [status(thm)], [c_34, c_4])).
% 2.02/1.23  tff(c_275, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_2, c_263])).
% 2.02/1.23  tff(c_447, plain, (k2_relat_1('#skF_1')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_438, c_438, c_275])).
% 2.02/1.23  tff(c_466, plain, $false, inference(negUnitSimplification, [status(thm)], [c_450, c_447])).
% 2.02/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.02/1.23  
% 2.02/1.23  Inference rules
% 2.02/1.23  ----------------------
% 2.02/1.23  #Ref     : 0
% 2.02/1.23  #Sup     : 103
% 2.02/1.23  #Fact    : 0
% 2.02/1.23  #Define  : 0
% 2.02/1.23  #Split   : 1
% 2.02/1.23  #Chain   : 0
% 2.02/1.23  #Close   : 0
% 2.02/1.23  
% 2.02/1.23  Ordering : KBO
% 2.02/1.23  
% 2.02/1.23  Simplification rules
% 2.02/1.23  ----------------------
% 2.02/1.23  #Subsume      : 2
% 2.02/1.23  #Demod        : 99
% 2.02/1.23  #Tautology    : 88
% 2.02/1.23  #SimpNegUnit  : 4
% 2.02/1.23  #BackRed      : 28
% 2.02/1.23  
% 2.02/1.23  #Partial instantiations: 0
% 2.02/1.23  #Strategies tried      : 1
% 2.02/1.23  
% 2.02/1.23  Timing (in seconds)
% 2.02/1.23  ----------------------
% 2.08/1.24  Preprocessing        : 0.26
% 2.08/1.24  Parsing              : 0.15
% 2.08/1.24  CNF conversion       : 0.01
% 2.08/1.24  Main loop            : 0.22
% 2.08/1.24  Inferencing          : 0.08
% 2.08/1.24  Reduction            : 0.06
% 2.08/1.24  Demodulation         : 0.05
% 2.08/1.24  BG Simplification    : 0.01
% 2.08/1.24  Subsumption          : 0.05
% 2.08/1.24  Abstraction          : 0.01
% 2.08/1.24  MUC search           : 0.00
% 2.08/1.24  Cooper               : 0.00
% 2.08/1.24  Total                : 0.51
% 2.08/1.24  Index Insertion      : 0.00
% 2.08/1.24  Index Deletion       : 0.00
% 2.08/1.24  Index Matching       : 0.00
% 2.08/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------

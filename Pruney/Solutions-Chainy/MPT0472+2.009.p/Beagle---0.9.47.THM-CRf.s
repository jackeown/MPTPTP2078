%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:59:26 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
% Verified   : 
% Statistics : Number of formulae       :   38 (  90 expanded)
%              Number of leaves         :   15 (  38 expanded)
%              Depth                    :    8
%              Number of atoms          :   50 ( 136 expanded)
%              Number of equality atoms :   19 (  64 expanded)
%              Maximal formula depth    :    6 (   3 average)
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

tff(f_56,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ( ( k1_relat_1(A) = k1_xboole_0
            | k2_relat_1(A) = k1_xboole_0 )
         => A = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_relat_1)).

tff(f_39,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k1_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc8_relat_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(c_4,plain,(
    v1_xboole_0('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_15,plain,(
    ! [A_4] :
      ( k1_xboole_0 = A_4
      | ~ v1_xboole_0(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_19,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_4,c_15])).

tff(c_10,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_21,plain,(
    '#skF_2' != '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19,c_10])).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,
    ( k2_relat_1('#skF_2') = k1_xboole_0
    | k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,
    ( k2_relat_1('#skF_2') = '#skF_1'
    | k1_relat_1('#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_19,c_19,c_12])).

tff(c_27,plain,(
    k1_relat_1('#skF_2') = '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_39,plain,(
    ! [A_7] :
      ( ~ v1_xboole_0(k1_relat_1(A_7))
      | ~ v1_relat_1(A_7)
      | v1_xboole_0(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_42,plain,
    ( ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_39])).

tff(c_44,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_4,c_42])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_1] :
      ( A_1 = '#skF_1'
      | ~ v1_xboole_0(A_1) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19,c_2])).

tff(c_47,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_44,c_20])).

tff(c_51,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21,c_47])).

tff(c_52,plain,(
    k2_relat_1('#skF_2') = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_58,plain,(
    ! [A_8] :
      ( ~ v1_xboole_0(k2_relat_1(A_8))
      | ~ v1_relat_1(A_8)
      | v1_xboole_0(A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_61,plain,
    ( ~ v1_xboole_0('#skF_1')
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_58])).

tff(c_63,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_4,c_61])).

tff(c_64,plain,(
    ! [A_9] :
      ( A_9 = '#skF_1'
      | ~ v1_xboole_0(A_9) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_19,c_2])).

tff(c_67,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_63,c_64])).

tff(c_74,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21,c_67])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n001.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:40:14 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.11  
% 1.58/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.11  %$ v1_xboole_0 > v1_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.58/1.11  
% 1.58/1.11  %Foreground sorts:
% 1.58/1.11  
% 1.58/1.11  
% 1.58/1.11  %Background operators:
% 1.58/1.11  
% 1.58/1.11  
% 1.58/1.11  %Foreground operators:
% 1.58/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.11  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.58/1.11  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.58/1.11  tff('#skF_2', type, '#skF_2': $i).
% 1.58/1.11  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.11  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.58/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.11  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.58/1.11  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.58/1.11  
% 1.58/1.12  tff(f_31, axiom, (?[A]: v1_xboole_0(A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', rc1_xboole_0)).
% 1.58/1.12  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.58/1.12  tff(f_56, negated_conjecture, ~(![A]: (v1_relat_1(A) => (((k1_relat_1(A) = k1_xboole_0) | (k2_relat_1(A) = k1_xboole_0)) => (A = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_relat_1)).
% 1.58/1.12  tff(f_39, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k1_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc8_relat_1)).
% 1.58/1.12  tff(f_47, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 1.58/1.12  tff(c_4, plain, (v1_xboole_0('#skF_1')), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.58/1.12  tff(c_15, plain, (![A_4]: (k1_xboole_0=A_4 | ~v1_xboole_0(A_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.58/1.12  tff(c_19, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_4, c_15])).
% 1.58/1.12  tff(c_10, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.58/1.12  tff(c_21, plain, ('#skF_2'!='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_19, c_10])).
% 1.58/1.12  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.58/1.12  tff(c_12, plain, (k2_relat_1('#skF_2')=k1_xboole_0 | k1_relat_1('#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.58/1.12  tff(c_26, plain, (k2_relat_1('#skF_2')='#skF_1' | k1_relat_1('#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_19, c_19, c_12])).
% 1.58/1.12  tff(c_27, plain, (k1_relat_1('#skF_2')='#skF_1'), inference(splitLeft, [status(thm)], [c_26])).
% 1.58/1.12  tff(c_39, plain, (![A_7]: (~v1_xboole_0(k1_relat_1(A_7)) | ~v1_relat_1(A_7) | v1_xboole_0(A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.58/1.12  tff(c_42, plain, (~v1_xboole_0('#skF_1') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_27, c_39])).
% 1.58/1.12  tff(c_44, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_4, c_42])).
% 1.58/1.12  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.58/1.12  tff(c_20, plain, (![A_1]: (A_1='#skF_1' | ~v1_xboole_0(A_1))), inference(demodulation, [status(thm), theory('equality')], [c_19, c_2])).
% 1.58/1.12  tff(c_47, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_44, c_20])).
% 1.58/1.12  tff(c_51, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21, c_47])).
% 1.58/1.12  tff(c_52, plain, (k2_relat_1('#skF_2')='#skF_1'), inference(splitRight, [status(thm)], [c_26])).
% 1.58/1.12  tff(c_58, plain, (![A_8]: (~v1_xboole_0(k2_relat_1(A_8)) | ~v1_relat_1(A_8) | v1_xboole_0(A_8))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.58/1.12  tff(c_61, plain, (~v1_xboole_0('#skF_1') | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_52, c_58])).
% 1.58/1.12  tff(c_63, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_4, c_61])).
% 1.58/1.12  tff(c_64, plain, (![A_9]: (A_9='#skF_1' | ~v1_xboole_0(A_9))), inference(demodulation, [status(thm), theory('equality')], [c_19, c_2])).
% 1.58/1.12  tff(c_67, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_63, c_64])).
% 1.58/1.12  tff(c_74, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21, c_67])).
% 1.58/1.12  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.12  
% 1.58/1.12  Inference rules
% 1.58/1.12  ----------------------
% 1.58/1.12  #Ref     : 0
% 1.58/1.12  #Sup     : 13
% 1.58/1.12  #Fact    : 0
% 1.58/1.12  #Define  : 0
% 1.58/1.12  #Split   : 1
% 1.58/1.12  #Chain   : 0
% 1.58/1.12  #Close   : 0
% 1.58/1.12  
% 1.58/1.12  Ordering : KBO
% 1.58/1.12  
% 1.58/1.12  Simplification rules
% 1.58/1.12  ----------------------
% 1.58/1.12  #Subsume      : 0
% 1.58/1.12  #Demod        : 8
% 1.58/1.12  #Tautology    : 7
% 1.58/1.12  #SimpNegUnit  : 2
% 1.58/1.12  #BackRed      : 2
% 1.58/1.12  
% 1.58/1.12  #Partial instantiations: 0
% 1.58/1.12  #Strategies tried      : 1
% 1.58/1.12  
% 1.58/1.12  Timing (in seconds)
% 1.58/1.12  ----------------------
% 1.58/1.12  Preprocessing        : 0.26
% 1.58/1.12  Parsing              : 0.15
% 1.58/1.12  CNF conversion       : 0.01
% 1.58/1.12  Main loop            : 0.09
% 1.58/1.12  Inferencing          : 0.04
% 1.58/1.12  Reduction            : 0.03
% 1.58/1.12  Demodulation         : 0.02
% 1.58/1.12  BG Simplification    : 0.01
% 1.58/1.12  Subsumption          : 0.01
% 1.58/1.12  Abstraction          : 0.00
% 1.58/1.12  MUC search           : 0.00
% 1.58/1.12  Cooper               : 0.00
% 1.58/1.12  Total                : 0.38
% 1.58/1.12  Index Insertion      : 0.00
% 1.58/1.12  Index Deletion       : 0.00
% 1.58/1.12  Index Matching       : 0.00
% 1.58/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------

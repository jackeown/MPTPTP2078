%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:10 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.81s
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
%$ v1_xboole_0 > v1_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_50,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( ( k2_relat_1(A) = k1_xboole_0
                & k2_relat_1(B) = k1_xboole_0 )
             => A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t197_relat_1)).

tff(f_26,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_38,axiom,(
    ! [A] :
      ( ( ~ v1_xboole_0(A)
        & v1_relat_1(A) )
     => ~ v1_xboole_0(k2_relat_1(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc9_relat_1)).

tff(f_30,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_8,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_26])).

tff(c_12,plain,(
    k2_relat_1('#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_31,plain,(
    ! [A_5] :
      ( ~ v1_xboole_0(k2_relat_1(A_5))
      | ~ v1_relat_1(A_5)
      | v1_xboole_0(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_34,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_1')
    | v1_xboole_0('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_31])).

tff(c_39,plain,(
    v1_xboole_0('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2,c_34])).

tff(c_4,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_30])).

tff(c_45,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_39,c_4])).

tff(c_14,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_10,plain,(
    k2_relat_1('#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_37,plain,
    ( ~ v1_xboole_0(k1_xboole_0)
    | ~ v1_relat_1('#skF_2')
    | v1_xboole_0('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_31])).

tff(c_41,plain,(
    v1_xboole_0('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_2,c_37])).

tff(c_49,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_41,c_4])).

tff(c_59,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_45,c_49])).

tff(c_60,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_8,c_59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:35:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.21  
% 1.74/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.22  %$ v1_xboole_0 > v1_relat_1 > #nlpp > k2_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.79/1.22  
% 1.79/1.22  %Foreground sorts:
% 1.79/1.22  
% 1.79/1.22  
% 1.79/1.22  %Background operators:
% 1.79/1.22  
% 1.79/1.22  
% 1.79/1.22  %Foreground operators:
% 1.79/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.22  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.79/1.22  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.22  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.22  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.79/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.79/1.22  
% 1.81/1.23  tff(f_50, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (((k2_relat_1(A) = k1_xboole_0) & (k2_relat_1(B) = k1_xboole_0)) => (A = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t197_relat_1)).
% 1.81/1.23  tff(f_26, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.81/1.23  tff(f_38, axiom, (![A]: ((~v1_xboole_0(A) & v1_relat_1(A)) => ~v1_xboole_0(k2_relat_1(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc9_relat_1)).
% 1.81/1.23  tff(f_30, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 1.81/1.23  tff(c_8, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.81/1.23  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.81/1.23  tff(c_2, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_26])).
% 1.81/1.23  tff(c_12, plain, (k2_relat_1('#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.81/1.23  tff(c_31, plain, (![A_5]: (~v1_xboole_0(k2_relat_1(A_5)) | ~v1_relat_1(A_5) | v1_xboole_0(A_5))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.81/1.23  tff(c_34, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_1') | v1_xboole_0('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_12, c_31])).
% 1.81/1.23  tff(c_39, plain, (v1_xboole_0('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2, c_34])).
% 1.81/1.23  tff(c_4, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_30])).
% 1.81/1.23  tff(c_45, plain, (k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_39, c_4])).
% 1.81/1.23  tff(c_14, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.81/1.23  tff(c_10, plain, (k2_relat_1('#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.81/1.23  tff(c_37, plain, (~v1_xboole_0(k1_xboole_0) | ~v1_relat_1('#skF_2') | v1_xboole_0('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_10, c_31])).
% 1.81/1.23  tff(c_41, plain, (v1_xboole_0('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_2, c_37])).
% 1.81/1.23  tff(c_49, plain, (k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_41, c_4])).
% 1.81/1.23  tff(c_59, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_45, c_49])).
% 1.81/1.23  tff(c_60, plain, $false, inference(negUnitSimplification, [status(thm)], [c_8, c_59])).
% 1.81/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.81/1.23  
% 1.81/1.23  Inference rules
% 1.81/1.23  ----------------------
% 1.81/1.23  #Ref     : 0
% 1.81/1.23  #Sup     : 11
% 1.81/1.23  #Fact    : 0
% 1.81/1.23  #Define  : 0
% 1.81/1.23  #Split   : 0
% 1.81/1.23  #Chain   : 0
% 1.81/1.23  #Close   : 0
% 1.81/1.23  
% 1.81/1.23  Ordering : KBO
% 1.81/1.23  
% 1.81/1.23  Simplification rules
% 1.81/1.23  ----------------------
% 1.81/1.23  #Subsume      : 0
% 1.81/1.23  #Demod        : 10
% 1.81/1.23  #Tautology    : 8
% 1.81/1.23  #SimpNegUnit  : 1
% 1.81/1.23  #BackRed      : 4
% 1.81/1.23  
% 1.81/1.23  #Partial instantiations: 0
% 1.81/1.23  #Strategies tried      : 1
% 1.81/1.23  
% 1.81/1.23  Timing (in seconds)
% 1.81/1.23  ----------------------
% 1.81/1.23  Preprocessing        : 0.28
% 1.81/1.23  Parsing              : 0.15
% 1.81/1.23  CNF conversion       : 0.02
% 1.81/1.23  Main loop            : 0.11
% 1.81/1.23  Inferencing          : 0.04
% 1.81/1.23  Reduction            : 0.04
% 1.81/1.23  Demodulation         : 0.03
% 1.81/1.23  BG Simplification    : 0.01
% 1.81/1.23  Subsumption          : 0.02
% 1.81/1.23  Abstraction          : 0.00
% 1.81/1.23  MUC search           : 0.00
% 1.81/1.23  Cooper               : 0.00
% 1.81/1.23  Total                : 0.43
% 1.81/1.23  Index Insertion      : 0.00
% 1.81/1.23  Index Deletion       : 0.00
% 1.81/1.23  Index Matching       : 0.00
% 1.81/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

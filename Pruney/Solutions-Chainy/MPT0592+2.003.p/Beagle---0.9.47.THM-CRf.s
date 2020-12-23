%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:02:10 EST 2020

% Result     : Theorem 1.65s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   27 (  39 expanded)
%              Number of leaves         :   12 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  68 expanded)
%              Number of equality atoms :   17 (  39 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

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

tff(k1_relat_1,type,(
    k1_relat_1: $i > $i )).

tff(f_45,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => ! [B] :
            ( v1_relat_1(B)
           => ( ( k1_relat_1(A) = k1_xboole_0
                & k1_relat_1(B) = k1_xboole_0 )
             => A = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t196_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_relat_1(A)) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_relat_1)).

tff(c_6,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_14,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_23,plain,(
    ! [A_4] :
      ( k7_relat_1(A_4,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_31,plain,(
    k7_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_23])).

tff(c_10,plain,(
    k1_relat_1('#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_40,plain,(
    ! [A_5] :
      ( k7_relat_1(A_5,k1_relat_1(A_5)) = A_5
      | ~ v1_relat_1(A_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_49,plain,
    ( k7_relat_1('#skF_1',k1_xboole_0) = '#skF_1'
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_40])).

tff(c_56,plain,(
    k1_xboole_0 = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_31,c_49])).

tff(c_12,plain,(
    v1_relat_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_30,plain,(
    k7_relat_1('#skF_2',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_23])).

tff(c_8,plain,(
    k1_relat_1('#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_52,plain,
    ( k7_relat_1('#skF_2',k1_xboole_0) = '#skF_2'
    | ~ v1_relat_1('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_40])).

tff(c_58,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_30,c_52])).

tff(c_68,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_58])).

tff(c_69,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_6,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n023.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:40:35 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.65/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.15  
% 1.65/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.15  %$ v1_relat_1 > k7_relat_1 > #nlpp > k1_relat_1 > k1_xboole_0 > #skF_2 > #skF_1
% 1.65/1.15  
% 1.65/1.15  %Foreground sorts:
% 1.65/1.15  
% 1.65/1.15  
% 1.65/1.15  %Background operators:
% 1.65/1.15  
% 1.65/1.15  
% 1.65/1.15  %Foreground operators:
% 1.65/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.65/1.15  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.65/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.65/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.65/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.65/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.65/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.65/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.65/1.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.65/1.15  
% 1.65/1.16  tff(f_45, negated_conjecture, ~(![A]: (v1_relat_1(A) => (![B]: (v1_relat_1(B) => (((k1_relat_1(A) = k1_xboole_0) & (k1_relat_1(B) = k1_xboole_0)) => (A = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t196_relat_1)).
% 1.65/1.16  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_relat_1)).
% 1.65/1.16  tff(f_33, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_relat_1(A)) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_relat_1)).
% 1.65/1.16  tff(c_6, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.65/1.16  tff(c_14, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.65/1.16  tff(c_23, plain, (![A_4]: (k7_relat_1(A_4, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.65/1.16  tff(c_31, plain, (k7_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_23])).
% 1.65/1.16  tff(c_10, plain, (k1_relat_1('#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.65/1.16  tff(c_40, plain, (![A_5]: (k7_relat_1(A_5, k1_relat_1(A_5))=A_5 | ~v1_relat_1(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.65/1.16  tff(c_49, plain, (k7_relat_1('#skF_1', k1_xboole_0)='#skF_1' | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_10, c_40])).
% 1.65/1.16  tff(c_56, plain, (k1_xboole_0='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_14, c_31, c_49])).
% 1.65/1.16  tff(c_12, plain, (v1_relat_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.65/1.16  tff(c_30, plain, (k7_relat_1('#skF_2', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_23])).
% 1.65/1.16  tff(c_8, plain, (k1_relat_1('#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.65/1.16  tff(c_52, plain, (k7_relat_1('#skF_2', k1_xboole_0)='#skF_2' | ~v1_relat_1('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_8, c_40])).
% 1.65/1.16  tff(c_58, plain, (k1_xboole_0='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_30, c_52])).
% 1.65/1.16  tff(c_68, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_56, c_58])).
% 1.65/1.16  tff(c_69, plain, $false, inference(negUnitSimplification, [status(thm)], [c_6, c_68])).
% 1.65/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.16  
% 1.65/1.16  Inference rules
% 1.65/1.16  ----------------------
% 1.65/1.16  #Ref     : 0
% 1.65/1.16  #Sup     : 16
% 1.65/1.16  #Fact    : 0
% 1.65/1.16  #Define  : 0
% 1.65/1.16  #Split   : 0
% 1.65/1.16  #Chain   : 0
% 1.65/1.16  #Close   : 0
% 1.65/1.16  
% 1.65/1.16  Ordering : KBO
% 1.65/1.16  
% 1.65/1.16  Simplification rules
% 1.65/1.16  ----------------------
% 1.65/1.16  #Subsume      : 0
% 1.65/1.16  #Demod        : 13
% 1.65/1.16  #Tautology    : 12
% 1.65/1.16  #SimpNegUnit  : 1
% 1.65/1.16  #BackRed      : 5
% 1.65/1.16  
% 1.65/1.16  #Partial instantiations: 0
% 1.65/1.16  #Strategies tried      : 1
% 1.65/1.16  
% 1.65/1.16  Timing (in seconds)
% 1.65/1.16  ----------------------
% 1.65/1.16  Preprocessing        : 0.30
% 1.65/1.16  Parsing              : 0.15
% 1.65/1.16  CNF conversion       : 0.02
% 1.65/1.16  Main loop            : 0.09
% 1.65/1.16  Inferencing          : 0.04
% 1.65/1.16  Reduction            : 0.03
% 1.65/1.16  Demodulation         : 0.02
% 1.65/1.16  BG Simplification    : 0.01
% 1.65/1.16  Subsumption          : 0.01
% 1.65/1.16  Abstraction          : 0.00
% 1.65/1.16  MUC search           : 0.00
% 1.65/1.16  Cooper               : 0.00
% 1.65/1.16  Total                : 0.42
% 1.65/1.16  Index Insertion      : 0.00
% 1.65/1.16  Index Deletion       : 0.00
% 1.65/1.16  Index Matching       : 0.00
% 1.65/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

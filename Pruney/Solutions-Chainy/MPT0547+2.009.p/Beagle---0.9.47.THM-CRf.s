%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:35 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   23 (  26 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  25 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k7_relat_1,type,(
    k7_relat_1: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k2_relat_1,type,(
    k2_relat_1: $i > $i )).

tff(k9_relat_1,type,(
    k9_relat_1: ( $i * $i ) > $i )).

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

tff(f_41,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_36,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_relat_1(A)
     => k7_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_relat_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_10,plain,(
    k9_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_12,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_6,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_21,plain,(
    ! [A_4] :
      ( k7_relat_1(A_4,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(A_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_25,plain,(
    k7_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_21])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( k2_relat_1(k7_relat_1(B_3,A_2)) = k9_relat_1(B_3,A_2)
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_38,plain,
    ( k9_relat_1('#skF_1',k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_4])).

tff(c_42,plain,(
    k9_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_6,c_38])).

tff(c_44,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_42])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.11  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.31  % Computer   : n025.cluster.edu
% 0.11/0.31  % Model      : x86_64 x86_64
% 0.11/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.31  % Memory     : 8042.1875MB
% 0.11/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.31  % CPULimit   : 60
% 0.11/0.31  % DateTime   : Tue Dec  1 10:06:50 EST 2020
% 0.17/0.31  % CPUTime    : 
% 0.17/0.32  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.04  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.04  
% 1.55/1.04  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.04  %$ v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.55/1.04  
% 1.55/1.04  %Foreground sorts:
% 1.55/1.04  
% 1.55/1.04  
% 1.55/1.04  %Background operators:
% 1.55/1.04  
% 1.55/1.04  
% 1.55/1.04  %Foreground operators:
% 1.55/1.04  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.55/1.04  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.55/1.04  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.55/1.04  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.55/1.04  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.55/1.04  tff('#skF_1', type, '#skF_1': $i).
% 1.55/1.04  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.55/1.04  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.55/1.04  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.55/1.04  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.55/1.04  
% 1.55/1.05  tff(f_41, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t149_relat_1)).
% 1.55/1.05  tff(f_36, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t60_relat_1)).
% 1.55/1.05  tff(f_29, axiom, (![A]: (v1_relat_1(A) => (k7_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_relat_1)).
% 1.55/1.05  tff(f_33, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_relat_1)).
% 1.55/1.05  tff(c_10, plain, (k9_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.55/1.05  tff(c_12, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.55/1.05  tff(c_6, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.55/1.05  tff(c_21, plain, (![A_4]: (k7_relat_1(A_4, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(A_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.55/1.05  tff(c_25, plain, (k7_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_21])).
% 1.55/1.05  tff(c_4, plain, (![B_3, A_2]: (k2_relat_1(k7_relat_1(B_3, A_2))=k9_relat_1(B_3, A_2) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.55/1.05  tff(c_38, plain, (k9_relat_1('#skF_1', k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_25, c_4])).
% 1.55/1.05  tff(c_42, plain, (k9_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_6, c_38])).
% 1.55/1.05  tff(c_44, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_42])).
% 1.55/1.05  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.05  
% 1.55/1.05  Inference rules
% 1.55/1.05  ----------------------
% 1.55/1.05  #Ref     : 0
% 1.55/1.05  #Sup     : 10
% 1.55/1.05  #Fact    : 0
% 1.55/1.05  #Define  : 0
% 1.55/1.05  #Split   : 0
% 1.55/1.05  #Chain   : 0
% 1.55/1.05  #Close   : 0
% 1.55/1.05  
% 1.55/1.05  Ordering : KBO
% 1.55/1.05  
% 1.55/1.05  Simplification rules
% 1.55/1.05  ----------------------
% 1.55/1.05  #Subsume      : 0
% 1.55/1.05  #Demod        : 2
% 1.55/1.05  #Tautology    : 7
% 1.55/1.05  #SimpNegUnit  : 1
% 1.55/1.05  #BackRed      : 0
% 1.55/1.05  
% 1.55/1.05  #Partial instantiations: 0
% 1.55/1.05  #Strategies tried      : 1
% 1.55/1.05  
% 1.55/1.05  Timing (in seconds)
% 1.55/1.05  ----------------------
% 1.55/1.05  Preprocessing        : 0.24
% 1.55/1.05  Parsing              : 0.13
% 1.55/1.05  CNF conversion       : 0.01
% 1.55/1.05  Main loop            : 0.07
% 1.55/1.05  Inferencing          : 0.04
% 1.55/1.05  Reduction            : 0.02
% 1.55/1.05  Demodulation         : 0.01
% 1.55/1.05  BG Simplification    : 0.01
% 1.55/1.05  Subsumption          : 0.01
% 1.55/1.05  Abstraction          : 0.00
% 1.55/1.05  MUC search           : 0.00
% 1.55/1.05  Cooper               : 0.00
% 1.55/1.05  Total                : 0.33
% 1.55/1.05  Index Insertion      : 0.00
% 1.55/1.05  Index Deletion       : 0.00
% 1.55/1.05  Index Matching       : 0.00
% 1.55/1.05  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:00:35 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   27 (  30 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  31 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_45,negated_conjecture,(
    ~ ! [A] :
        ( v1_relat_1(A)
       => k9_relat_1(A,k1_xboole_0) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t149_relat_1)).

tff(f_34,axiom,
    ( k1_relat_1(k1_xboole_0) = k1_xboole_0
    & k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t60_relat_1)).

tff(f_27,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => ( k7_relat_1(B,A) = k1_xboole_0
      <=> r1_xboole_0(k1_relat_1(B),A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_relat_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_relat_1(B)
     => k2_relat_1(k7_relat_1(B,A)) = k9_relat_1(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_relat_1)).

tff(c_14,plain,(
    k9_relat_1('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_16,plain,(
    v1_relat_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    k2_relat_1(k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    ! [A_1] : r1_xboole_0(A_1,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_35,plain,(
    ! [B_9,A_10] :
      ( k7_relat_1(B_9,A_10) = k1_xboole_0
      | ~ r1_xboole_0(k1_relat_1(B_9),A_10)
      | ~ v1_relat_1(B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_44,plain,(
    ! [B_11] :
      ( k7_relat_1(B_11,k1_xboole_0) = k1_xboole_0
      | ~ v1_relat_1(B_11) ) ),
    inference(resolution,[status(thm)],[c_2,c_35])).

tff(c_48,plain,(
    k7_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_16,c_44])).

tff(c_4,plain,(
    ! [B_3,A_2] :
      ( k2_relat_1(k7_relat_1(B_3,A_2)) = k9_relat_1(B_3,A_2)
      | ~ v1_relat_1(B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,
    ( k9_relat_1('#skF_1',k1_xboole_0) = k2_relat_1(k1_xboole_0)
    | ~ v1_relat_1('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_4])).

tff(c_56,plain,(
    k9_relat_1('#skF_1',k1_xboole_0) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_6,c_52])).

tff(c_58,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:32:04 EST 2020
% 0.19/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.15  
% 1.60/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.15  %$ r1_xboole_0 > v1_relat_1 > k9_relat_1 > k7_relat_1 > #nlpp > k2_relat_1 > k1_relat_1 > k1_xboole_0 > #skF_1
% 1.60/1.15  
% 1.60/1.15  %Foreground sorts:
% 1.60/1.15  
% 1.60/1.15  
% 1.60/1.15  %Background operators:
% 1.60/1.15  
% 1.60/1.15  
% 1.60/1.15  %Foreground operators:
% 1.60/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.15  tff(k7_relat_1, type, k7_relat_1: ($i * $i) > $i).
% 1.60/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.15  tff(k2_relat_1, type, k2_relat_1: $i > $i).
% 1.60/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.60/1.15  tff(k9_relat_1, type, k9_relat_1: ($i * $i) > $i).
% 1.60/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.15  tff(v1_relat_1, type, v1_relat_1: $i > $o).
% 1.60/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.15  tff(k1_relat_1, type, k1_relat_1: $i > $i).
% 1.60/1.15  
% 1.60/1.16  tff(f_45, negated_conjecture, ~(![A]: (v1_relat_1(A) => (k9_relat_1(A, k1_xboole_0) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t149_relat_1)).
% 1.60/1.16  tff(f_34, axiom, ((k1_relat_1(k1_xboole_0) = k1_xboole_0) & (k2_relat_1(k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t60_relat_1)).
% 1.60/1.16  tff(f_27, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.60/1.16  tff(f_40, axiom, (![A, B]: (v1_relat_1(B) => ((k7_relat_1(B, A) = k1_xboole_0) <=> r1_xboole_0(k1_relat_1(B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_relat_1)).
% 1.60/1.16  tff(f_31, axiom, (![A, B]: (v1_relat_1(B) => (k2_relat_1(k7_relat_1(B, A)) = k9_relat_1(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_relat_1)).
% 1.60/1.16  tff(c_14, plain, (k9_relat_1('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.60/1.16  tff(c_16, plain, (v1_relat_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.60/1.16  tff(c_6, plain, (k2_relat_1(k1_xboole_0)=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.60/1.16  tff(c_2, plain, (![A_1]: (r1_xboole_0(A_1, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.60/1.16  tff(c_35, plain, (![B_9, A_10]: (k7_relat_1(B_9, A_10)=k1_xboole_0 | ~r1_xboole_0(k1_relat_1(B_9), A_10) | ~v1_relat_1(B_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.60/1.16  tff(c_44, plain, (![B_11]: (k7_relat_1(B_11, k1_xboole_0)=k1_xboole_0 | ~v1_relat_1(B_11))), inference(resolution, [status(thm)], [c_2, c_35])).
% 1.60/1.16  tff(c_48, plain, (k7_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_16, c_44])).
% 1.60/1.16  tff(c_4, plain, (![B_3, A_2]: (k2_relat_1(k7_relat_1(B_3, A_2))=k9_relat_1(B_3, A_2) | ~v1_relat_1(B_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.60/1.16  tff(c_52, plain, (k9_relat_1('#skF_1', k1_xboole_0)=k2_relat_1(k1_xboole_0) | ~v1_relat_1('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_48, c_4])).
% 1.60/1.16  tff(c_56, plain, (k9_relat_1('#skF_1', k1_xboole_0)=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_6, c_52])).
% 1.60/1.16  tff(c_58, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_56])).
% 1.60/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.60/1.16  
% 1.60/1.16  Inference rules
% 1.60/1.16  ----------------------
% 1.60/1.16  #Ref     : 0
% 1.60/1.16  #Sup     : 12
% 1.60/1.16  #Fact    : 0
% 1.60/1.16  #Define  : 0
% 1.60/1.16  #Split   : 0
% 1.60/1.16  #Chain   : 0
% 1.60/1.16  #Close   : 0
% 1.60/1.16  
% 1.60/1.16  Ordering : KBO
% 1.60/1.16  
% 1.60/1.16  Simplification rules
% 1.60/1.16  ----------------------
% 1.60/1.16  #Subsume      : 0
% 1.60/1.16  #Demod        : 2
% 1.60/1.16  #Tautology    : 7
% 1.60/1.16  #SimpNegUnit  : 1
% 1.60/1.16  #BackRed      : 0
% 1.60/1.16  
% 1.60/1.16  #Partial instantiations: 0
% 1.60/1.16  #Strategies tried      : 1
% 1.60/1.16  
% 1.60/1.16  Timing (in seconds)
% 1.60/1.16  ----------------------
% 1.60/1.17  Preprocessing        : 0.27
% 1.60/1.17  Parsing              : 0.16
% 1.60/1.17  CNF conversion       : 0.01
% 1.60/1.17  Main loop            : 0.09
% 1.60/1.17  Inferencing          : 0.04
% 1.60/1.17  Reduction            : 0.02
% 1.60/1.17  Demodulation         : 0.02
% 1.78/1.17  BG Simplification    : 0.01
% 1.78/1.17  Subsumption          : 0.01
% 1.78/1.17  Abstraction          : 0.00
% 1.78/1.17  MUC search           : 0.00
% 1.78/1.17  Cooper               : 0.00
% 1.78/1.17  Total                : 0.38
% 1.78/1.17  Index Insertion      : 0.00
% 1.78/1.17  Index Deletion       : 0.00
% 1.78/1.17  Index Matching       : 0.00
% 1.78/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------

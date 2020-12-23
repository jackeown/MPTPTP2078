%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:42 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.74s
% Verified   : 
% Statistics : Number of formulae       :   32 (  40 expanded)
%              Number of leaves         :   15 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  45 expanded)
%              Number of equality atoms :   19 (  30 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_42,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_10,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_14,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_21,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = k1_xboole_0
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_29,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_21])).

tff(c_43,plain,(
    ! [A_11,B_12] : k2_xboole_0(k3_xboole_0(A_11,B_12),k4_xboole_0(A_11,B_12)) = A_11 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_52,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_2')) = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_29,c_43])).

tff(c_6,plain,(
    ! [A_3,B_4] : k4_xboole_0(k2_xboole_0(A_3,B_4),B_4) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_66,plain,(
    ! [A_13,B_14] : k4_xboole_0(k2_xboole_0(A_13,B_14),B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_87,plain,(
    k4_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_2') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_66])).

tff(c_90,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_87])).

tff(c_12,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_28,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_12,c_21])).

tff(c_55,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_2')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_43])).

tff(c_91,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_1','#skF_2')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_90,c_55])).

tff(c_92,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_91])).

tff(c_94,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_10,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:50:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.29  
% 1.74/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.29  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.74/1.29  
% 1.74/1.29  %Foreground sorts:
% 1.74/1.29  
% 1.74/1.29  
% 1.74/1.29  %Background operators:
% 1.74/1.29  
% 1.74/1.29  
% 1.74/1.29  %Foreground operators:
% 1.74/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.74/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.74/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.74/1.29  tff('#skF_2', type, '#skF_2': $i).
% 1.74/1.29  tff('#skF_3', type, '#skF_3': $i).
% 1.74/1.29  tff('#skF_1', type, '#skF_1': $i).
% 1.74/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.74/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.74/1.29  
% 1.74/1.30  tff(f_42, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_xboole_1)).
% 1.74/1.30  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.74/1.30  tff(f_33, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 1.74/1.30  tff(f_31, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 1.74/1.30  tff(c_10, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.74/1.30  tff(c_14, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.74/1.30  tff(c_21, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=k1_xboole_0 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.74/1.30  tff(c_29, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_14, c_21])).
% 1.74/1.30  tff(c_43, plain, (![A_11, B_12]: (k2_xboole_0(k3_xboole_0(A_11, B_12), k4_xboole_0(A_11, B_12))=A_11)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.74/1.30  tff(c_52, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_2'))='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_29, c_43])).
% 1.74/1.30  tff(c_6, plain, (![A_3, B_4]: (k4_xboole_0(k2_xboole_0(A_3, B_4), B_4)=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.74/1.30  tff(c_16, plain, (k2_xboole_0('#skF_3', '#skF_2')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.74/1.30  tff(c_66, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.74/1.30  tff(c_87, plain, (k4_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_16, c_66])).
% 1.74/1.30  tff(c_90, plain, (k4_xboole_0('#skF_3', '#skF_2')=k4_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_6, c_87])).
% 1.74/1.30  tff(c_12, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.74/1.30  tff(c_28, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_12, c_21])).
% 1.74/1.30  tff(c_55, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_2'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_28, c_43])).
% 1.74/1.30  tff(c_91, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_1', '#skF_2'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_90, c_55])).
% 1.74/1.30  tff(c_92, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_52, c_91])).
% 1.74/1.30  tff(c_94, plain, $false, inference(negUnitSimplification, [status(thm)], [c_10, c_92])).
% 1.74/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.74/1.30  
% 1.74/1.30  Inference rules
% 1.74/1.30  ----------------------
% 1.74/1.30  #Ref     : 0
% 1.74/1.30  #Sup     : 24
% 1.74/1.30  #Fact    : 0
% 1.74/1.30  #Define  : 0
% 1.74/1.30  #Split   : 0
% 1.74/1.30  #Chain   : 0
% 1.74/1.30  #Close   : 0
% 1.74/1.30  
% 1.74/1.30  Ordering : KBO
% 1.74/1.30  
% 1.74/1.30  Simplification rules
% 1.74/1.30  ----------------------
% 1.74/1.30  #Subsume      : 0
% 1.74/1.30  #Demod        : 3
% 1.74/1.30  #Tautology    : 15
% 1.74/1.30  #SimpNegUnit  : 1
% 1.74/1.30  #BackRed      : 1
% 1.74/1.30  
% 1.74/1.30  #Partial instantiations: 0
% 1.74/1.30  #Strategies tried      : 1
% 1.74/1.30  
% 1.74/1.30  Timing (in seconds)
% 1.74/1.30  ----------------------
% 1.74/1.31  Preprocessing        : 0.31
% 1.74/1.31  Parsing              : 0.17
% 1.74/1.31  CNF conversion       : 0.01
% 1.74/1.31  Main loop            : 0.09
% 1.74/1.31  Inferencing          : 0.04
% 1.74/1.31  Reduction            : 0.03
% 1.74/1.31  Demodulation         : 0.02
% 1.74/1.31  BG Simplification    : 0.01
% 1.74/1.31  Subsumption          : 0.01
% 1.74/1.31  Abstraction          : 0.00
% 1.74/1.31  MUC search           : 0.00
% 1.74/1.31  Cooper               : 0.00
% 1.74/1.31  Total                : 0.43
% 1.74/1.31  Index Insertion      : 0.00
% 1.74/1.31  Index Deletion       : 0.00
% 1.74/1.31  Index Matching       : 0.00
% 1.74/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------

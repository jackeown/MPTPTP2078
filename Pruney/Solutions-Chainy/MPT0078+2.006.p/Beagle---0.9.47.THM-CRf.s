%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:39 EST 2020

% Result     : Theorem 2.27s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   43 (  70 expanded)
%              Number of leaves         :   18 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   37 (  75 expanded)
%              Number of equality atoms :   30 (  60 expanded)
%              Maximal formula depth    :    8 (   2 average)
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

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_26,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_151,plain,(
    ! [B_29,A_30] : k2_xboole_0(B_29,A_30) = k2_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_9] : k2_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_167,plain,(
    ! [A_30] : k2_xboole_0(k1_xboole_0,A_30) = A_30 ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_12])).

tff(c_438,plain,(
    ! [A_44,B_45] : k2_xboole_0(A_44,k4_xboole_0(B_45,A_44)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_448,plain,(
    ! [B_45] : k4_xboole_0(B_45,k1_xboole_0) = k2_xboole_0(k1_xboole_0,B_45) ),
    inference(superposition,[status(thm),theory(equality)],[c_438,c_167])).

tff(c_487,plain,(
    ! [B_45] : k4_xboole_0(B_45,k1_xboole_0) = B_45 ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_448])).

tff(c_30,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_241,plain,(
    ! [A_34,B_35] :
      ( k3_xboole_0(A_34,B_35) = k1_xboole_0
      | ~ r1_xboole_0(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_261,plain,(
    k3_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_30,c_241])).

tff(c_366,plain,(
    ! [A_41,B_42] : k4_xboole_0(A_41,k3_xboole_0(A_41,B_42)) = k4_xboole_0(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_381,plain,(
    k4_xboole_0('#skF_1',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_366])).

tff(c_502,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_381])).

tff(c_18,plain,(
    ! [A_13,B_14] : k4_xboole_0(k2_xboole_0(A_13,B_14),B_14) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_32,plain,(
    k2_xboole_0('#skF_3','#skF_2') = k2_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_311,plain,(
    ! [A_36,B_37] : k4_xboole_0(k2_xboole_0(A_36,B_37),B_37) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_329,plain,(
    k4_xboole_0(k2_xboole_0('#skF_1','#skF_2'),'#skF_2') = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_311])).

tff(c_335,plain,(
    k4_xboole_0('#skF_3','#skF_2') = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_329])).

tff(c_28,plain,(
    r1_xboole_0('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_260,plain,(
    k3_xboole_0('#skF_3','#skF_2') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_28,c_241])).

tff(c_384,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_260,c_366])).

tff(c_399,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_1','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_335,c_384])).

tff(c_501,plain,(
    k4_xboole_0('#skF_1','#skF_2') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_399])).

tff(c_597,plain,(
    '#skF_3' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_502,c_501])).

tff(c_598,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_26,c_597])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n003.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:25:27 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.27/1.34  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.35  
% 2.27/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.35  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.27/1.35  
% 2.27/1.35  %Foreground sorts:
% 2.27/1.35  
% 2.27/1.35  
% 2.27/1.35  %Background operators:
% 2.27/1.35  
% 2.27/1.35  
% 2.27/1.35  %Foreground operators:
% 2.27/1.35  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.27/1.35  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.27/1.35  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.27/1.35  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.27/1.35  tff('#skF_2', type, '#skF_2': $i).
% 2.27/1.35  tff('#skF_3', type, '#skF_3': $i).
% 2.27/1.35  tff('#skF_1', type, '#skF_1': $i).
% 2.27/1.35  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.27/1.35  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.27/1.35  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.27/1.35  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.27/1.35  
% 2.27/1.36  tff(f_60, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_xboole_1)).
% 2.27/1.36  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.27/1.36  tff(f_39, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.27/1.36  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.27/1.36  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 2.27/1.36  tff(f_49, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.27/1.36  tff(f_45, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.27/1.36  tff(c_26, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.27/1.36  tff(c_151, plain, (![B_29, A_30]: (k2_xboole_0(B_29, A_30)=k2_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.27/1.36  tff(c_12, plain, (![A_9]: (k2_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.27/1.36  tff(c_167, plain, (![A_30]: (k2_xboole_0(k1_xboole_0, A_30)=A_30)), inference(superposition, [status(thm), theory('equality')], [c_151, c_12])).
% 2.27/1.36  tff(c_438, plain, (![A_44, B_45]: (k2_xboole_0(A_44, k4_xboole_0(B_45, A_44))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.27/1.36  tff(c_448, plain, (![B_45]: (k4_xboole_0(B_45, k1_xboole_0)=k2_xboole_0(k1_xboole_0, B_45))), inference(superposition, [status(thm), theory('equality')], [c_438, c_167])).
% 2.27/1.36  tff(c_487, plain, (![B_45]: (k4_xboole_0(B_45, k1_xboole_0)=B_45)), inference(demodulation, [status(thm), theory('equality')], [c_167, c_448])).
% 2.27/1.36  tff(c_30, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.27/1.36  tff(c_241, plain, (![A_34, B_35]: (k3_xboole_0(A_34, B_35)=k1_xboole_0 | ~r1_xboole_0(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.27/1.36  tff(c_261, plain, (k3_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_30, c_241])).
% 2.27/1.36  tff(c_366, plain, (![A_41, B_42]: (k4_xboole_0(A_41, k3_xboole_0(A_41, B_42))=k4_xboole_0(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.27/1.36  tff(c_381, plain, (k4_xboole_0('#skF_1', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_261, c_366])).
% 2.27/1.36  tff(c_502, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_487, c_381])).
% 2.27/1.36  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), B_14)=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.27/1.36  tff(c_32, plain, (k2_xboole_0('#skF_3', '#skF_2')=k2_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.27/1.36  tff(c_311, plain, (![A_36, B_37]: (k4_xboole_0(k2_xboole_0(A_36, B_37), B_37)=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.27/1.36  tff(c_329, plain, (k4_xboole_0(k2_xboole_0('#skF_1', '#skF_2'), '#skF_2')=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_32, c_311])).
% 2.27/1.36  tff(c_335, plain, (k4_xboole_0('#skF_3', '#skF_2')=k4_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_329])).
% 2.27/1.36  tff(c_28, plain, (r1_xboole_0('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.27/1.36  tff(c_260, plain, (k3_xboole_0('#skF_3', '#skF_2')=k1_xboole_0), inference(resolution, [status(thm)], [c_28, c_241])).
% 2.27/1.36  tff(c_384, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_260, c_366])).
% 2.27/1.36  tff(c_399, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_1', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_335, c_384])).
% 2.27/1.36  tff(c_501, plain, (k4_xboole_0('#skF_1', '#skF_2')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_487, c_399])).
% 2.27/1.36  tff(c_597, plain, ('#skF_3'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_502, c_501])).
% 2.27/1.36  tff(c_598, plain, $false, inference(negUnitSimplification, [status(thm)], [c_26, c_597])).
% 2.27/1.36  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.27/1.36  
% 2.27/1.36  Inference rules
% 2.27/1.36  ----------------------
% 2.27/1.36  #Ref     : 0
% 2.27/1.36  #Sup     : 150
% 2.27/1.36  #Fact    : 0
% 2.27/1.36  #Define  : 0
% 2.27/1.36  #Split   : 0
% 2.27/1.36  #Chain   : 0
% 2.27/1.36  #Close   : 0
% 2.27/1.36  
% 2.27/1.36  Ordering : KBO
% 2.27/1.36  
% 2.27/1.36  Simplification rules
% 2.27/1.36  ----------------------
% 2.27/1.36  #Subsume      : 5
% 2.27/1.36  #Demod        : 65
% 2.27/1.36  #Tautology    : 108
% 2.27/1.36  #SimpNegUnit  : 1
% 2.27/1.36  #BackRed      : 7
% 2.27/1.36  
% 2.27/1.36  #Partial instantiations: 0
% 2.27/1.36  #Strategies tried      : 1
% 2.27/1.36  
% 2.27/1.36  Timing (in seconds)
% 2.27/1.36  ----------------------
% 2.27/1.37  Preprocessing        : 0.30
% 2.27/1.37  Parsing              : 0.16
% 2.27/1.37  CNF conversion       : 0.02
% 2.27/1.37  Main loop            : 0.25
% 2.27/1.37  Inferencing          : 0.09
% 2.27/1.37  Reduction            : 0.09
% 2.27/1.37  Demodulation         : 0.07
% 2.27/1.37  BG Simplification    : 0.01
% 2.27/1.37  Subsumption          : 0.04
% 2.27/1.37  Abstraction          : 0.01
% 2.27/1.37  MUC search           : 0.00
% 2.27/1.37  Cooper               : 0.00
% 2.27/1.37  Total                : 0.58
% 2.27/1.37  Index Insertion      : 0.00
% 2.27/1.37  Index Deletion       : 0.00
% 2.27/1.37  Index Matching       : 0.00
% 2.27/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------

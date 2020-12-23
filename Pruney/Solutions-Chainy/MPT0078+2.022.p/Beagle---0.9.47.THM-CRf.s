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
% DateTime   : Thu Dec  3 09:43:41 EST 2020

% Result     : Theorem 2.40s
% Output     : CNFRefutation 2.40s
% Verified   : 
% Statistics : Number of formulae       :   46 (  70 expanded)
%              Number of leaves         :   21 (  34 expanded)
%              Depth                    :    7
%              Number of atoms          :   42 (  82 expanded)
%              Number of equality atoms :   28 (  53 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_20,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_24,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_144,plain,(
    ! [A_26,B_27,C_28] :
      ( ~ r1_xboole_0(A_26,B_27)
      | ~ r2_hidden(C_28,k3_xboole_0(A_26,B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_150,plain,(
    ! [A_29,B_30] :
      ( ~ r1_xboole_0(A_29,B_30)
      | k3_xboole_0(A_29,B_30) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_144])).

tff(c_158,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_150])).

tff(c_347,plain,(
    ! [A_39,B_40] : k2_xboole_0(k3_xboole_0(A_39,B_40),k4_xboole_0(A_39,B_40)) = A_39 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_371,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_347])).

tff(c_42,plain,(
    ! [B_21,A_22] : k2_xboole_0(B_21,A_22) = k2_xboole_0(A_22,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10] : k2_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_58,plain,(
    ! [A_22] : k2_xboole_0(k1_xboole_0,A_22) = A_22 ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_10])).

tff(c_391,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_371,c_58])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_255,plain,(
    ! [A_36,B_37] : k4_xboole_0(k2_xboole_0(A_36,B_37),B_37) = k4_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_287,plain,(
    ! [A_1,B_2] : k4_xboole_0(k2_xboole_0(A_1,B_2),A_1) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_255])).

tff(c_22,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_157,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_150])).

tff(c_377,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_5','#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_347])).

tff(c_424,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_377,c_58])).

tff(c_26,plain,(
    k2_xboole_0('#skF_5','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_27,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_26])).

tff(c_602,plain,(
    ! [A_43,B_44] : k4_xboole_0(k2_xboole_0(A_43,B_44),A_43) = k4_xboole_0(B_44,A_43) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_255])).

tff(c_657,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_4') = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_27,c_602])).

tff(c_674,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_391,c_287,c_424,c_657])).

tff(c_676,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_674])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:39:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.40/1.33  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.34  
% 2.40/1.34  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.34  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.40/1.34  
% 2.40/1.34  %Foreground sorts:
% 2.40/1.34  
% 2.40/1.34  
% 2.40/1.34  %Background operators:
% 2.40/1.34  
% 2.40/1.34  
% 2.40/1.34  %Foreground operators:
% 2.40/1.34  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.40/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.40/1.34  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.40/1.34  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.40/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.40/1.34  tff('#skF_5', type, '#skF_5': $i).
% 2.40/1.34  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.40/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.40/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.40/1.34  tff('#skF_4', type, '#skF_4': $i).
% 2.40/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.40/1.34  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.40/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.40/1.34  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.40/1.34  
% 2.40/1.35  tff(f_68, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_xboole_1)).
% 2.40/1.35  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.40/1.35  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.40/1.35  tff(f_59, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.40/1.35  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.40/1.35  tff(f_51, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 2.40/1.35  tff(f_55, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.40/1.35  tff(c_20, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.40/1.35  tff(c_24, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.40/1.35  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.40/1.35  tff(c_144, plain, (![A_26, B_27, C_28]: (~r1_xboole_0(A_26, B_27) | ~r2_hidden(C_28, k3_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.40/1.35  tff(c_150, plain, (![A_29, B_30]: (~r1_xboole_0(A_29, B_30) | k3_xboole_0(A_29, B_30)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_144])).
% 2.40/1.35  tff(c_158, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_150])).
% 2.40/1.35  tff(c_347, plain, (![A_39, B_40]: (k2_xboole_0(k3_xboole_0(A_39, B_40), k4_xboole_0(A_39, B_40))=A_39)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.40/1.35  tff(c_371, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_158, c_347])).
% 2.40/1.35  tff(c_42, plain, (![B_21, A_22]: (k2_xboole_0(B_21, A_22)=k2_xboole_0(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.40/1.35  tff(c_10, plain, (![A_10]: (k2_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.40/1.35  tff(c_58, plain, (![A_22]: (k2_xboole_0(k1_xboole_0, A_22)=A_22)), inference(superposition, [status(thm), theory('equality')], [c_42, c_10])).
% 2.40/1.35  tff(c_391, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_371, c_58])).
% 2.40/1.35  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.40/1.35  tff(c_255, plain, (![A_36, B_37]: (k4_xboole_0(k2_xboole_0(A_36, B_37), B_37)=k4_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.40/1.35  tff(c_287, plain, (![A_1, B_2]: (k4_xboole_0(k2_xboole_0(A_1, B_2), A_1)=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_255])).
% 2.40/1.35  tff(c_22, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.40/1.35  tff(c_157, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_150])).
% 2.40/1.35  tff(c_377, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_5', '#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_157, c_347])).
% 2.40/1.35  tff(c_424, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_377, c_58])).
% 2.40/1.35  tff(c_26, plain, (k2_xboole_0('#skF_5', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.40/1.35  tff(c_27, plain, (k2_xboole_0('#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_26])).
% 2.40/1.35  tff(c_602, plain, (![A_43, B_44]: (k4_xboole_0(k2_xboole_0(A_43, B_44), A_43)=k4_xboole_0(B_44, A_43))), inference(superposition, [status(thm), theory('equality')], [c_2, c_255])).
% 2.40/1.35  tff(c_657, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_27, c_602])).
% 2.40/1.35  tff(c_674, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_391, c_287, c_424, c_657])).
% 2.40/1.35  tff(c_676, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_674])).
% 2.40/1.35  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.40/1.35  
% 2.40/1.35  Inference rules
% 2.40/1.35  ----------------------
% 2.40/1.35  #Ref     : 0
% 2.40/1.35  #Sup     : 174
% 2.40/1.35  #Fact    : 0
% 2.40/1.35  #Define  : 0
% 2.40/1.35  #Split   : 0
% 2.40/1.35  #Chain   : 0
% 2.40/1.35  #Close   : 0
% 2.40/1.35  
% 2.40/1.35  Ordering : KBO
% 2.40/1.35  
% 2.40/1.35  Simplification rules
% 2.40/1.35  ----------------------
% 2.40/1.35  #Subsume      : 4
% 2.40/1.35  #Demod        : 107
% 2.40/1.35  #Tautology    : 110
% 2.40/1.35  #SimpNegUnit  : 6
% 2.40/1.35  #BackRed      : 2
% 2.40/1.35  
% 2.40/1.35  #Partial instantiations: 0
% 2.40/1.35  #Strategies tried      : 1
% 2.40/1.35  
% 2.40/1.35  Timing (in seconds)
% 2.40/1.35  ----------------------
% 2.40/1.35  Preprocessing        : 0.29
% 2.40/1.35  Parsing              : 0.16
% 2.40/1.35  CNF conversion       : 0.02
% 2.40/1.35  Main loop            : 0.29
% 2.40/1.35  Inferencing          : 0.10
% 2.40/1.35  Reduction            : 0.11
% 2.40/1.35  Demodulation         : 0.09
% 2.40/1.35  BG Simplification    : 0.01
% 2.40/1.35  Subsumption          : 0.04
% 2.40/1.35  Abstraction          : 0.01
% 2.40/1.35  MUC search           : 0.00
% 2.40/1.36  Cooper               : 0.00
% 2.40/1.36  Total                : 0.61
% 2.40/1.36  Index Insertion      : 0.00
% 2.40/1.36  Index Deletion       : 0.00
% 2.40/1.36  Index Matching       : 0.00
% 2.40/1.36  BG Taut test         : 0.00
%------------------------------------------------------------------------------

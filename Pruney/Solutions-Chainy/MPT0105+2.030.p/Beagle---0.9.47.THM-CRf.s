%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:51 EST 2020

% Result     : Theorem 2.91s
% Output     : CNFRefutation 2.91s
% Verified   : 
% Statistics : Number of formulae       :   31 (  42 expanded)
%              Number of leaves         :   15 (  22 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  73 expanded)
%              Number of equality atoms :   18 (  29 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k2_xboole_0(k4_xboole_0(A,B),k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d6_xboole_0)).

tff(f_42,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_22,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_60,plain,(
    ! [A_27,B_28,C_29] :
      ( r2_hidden('#skF_1'(A_27,B_28,C_29),A_27)
      | r2_hidden('#skF_2'(A_27,B_28,C_29),C_29)
      | k4_xboole_0(A_27,B_28) = C_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_81,plain,(
    ! [A_27,B_28] :
      ( r2_hidden('#skF_2'(A_27,B_28,A_27),A_27)
      | k4_xboole_0(A_27,B_28) = A_27 ) ),
    inference(resolution,[status(thm)],[c_60,c_14])).

tff(c_444,plain,(
    ! [A_65,B_66,C_67] :
      ( r2_hidden('#skF_1'(A_65,B_66,C_67),A_65)
      | r2_hidden('#skF_2'(A_65,B_66,C_67),B_66)
      | ~ r2_hidden('#skF_2'(A_65,B_66,C_67),A_65)
      | k4_xboole_0(A_65,B_66) = C_67 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8,plain,(
    ! [A_1,B_2,C_3] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2,C_3),C_3)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_773,plain,(
    ! [A_76,B_77] :
      ( r2_hidden('#skF_2'(A_76,B_77,A_76),B_77)
      | ~ r2_hidden('#skF_2'(A_76,B_77,A_76),A_76)
      | k4_xboole_0(A_76,B_77) = A_76 ) ),
    inference(resolution,[status(thm)],[c_444,c_8])).

tff(c_787,plain,(
    ! [A_78,B_79] :
      ( r2_hidden('#skF_2'(A_78,B_79,A_78),B_79)
      | k4_xboole_0(A_78,B_79) = A_78 ) ),
    inference(resolution,[status(thm)],[c_81,c_773])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_826,plain,(
    ! [A_84,A_85,B_86] :
      ( ~ r2_hidden('#skF_2'(A_84,k4_xboole_0(A_85,B_86),A_84),B_86)
      | k4_xboole_0(A_84,k4_xboole_0(A_85,B_86)) = A_84 ) ),
    inference(resolution,[status(thm)],[c_787,c_4])).

tff(c_850,plain,(
    ! [A_87,A_88] : k4_xboole_0(A_87,k4_xboole_0(A_88,A_87)) = A_87 ),
    inference(resolution,[status(thm)],[c_81,c_826])).

tff(c_20,plain,(
    ! [A_7,B_8] : k2_xboole_0(k4_xboole_0(A_7,B_8),k4_xboole_0(B_8,A_7)) = k5_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_873,plain,(
    ! [A_87,A_88] : k2_xboole_0(A_87,k4_xboole_0(k4_xboole_0(A_88,A_87),A_87)) = k5_xboole_0(A_87,k4_xboole_0(A_88,A_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_850,c_20])).

tff(c_903,plain,(
    ! [A_87,A_88] : k5_xboole_0(A_87,k4_xboole_0(A_88,A_87)) = k2_xboole_0(A_87,A_88) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_22,c_873])).

tff(c_24,plain,(
    k5_xboole_0('#skF_3',k4_xboole_0('#skF_4','#skF_3')) != k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_1202,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_903,c_24])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:29:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.91/1.41  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.41  
% 2.91/1.41  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.41  %$ r2_hidden > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.91/1.41  
% 2.91/1.41  %Foreground sorts:
% 2.91/1.41  
% 2.91/1.41  
% 2.91/1.41  %Background operators:
% 2.91/1.41  
% 2.91/1.41  
% 2.91/1.41  %Foreground operators:
% 2.91/1.41  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.91/1.41  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.91/1.41  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.91/1.41  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.91/1.41  tff('#skF_3', type, '#skF_3': $i).
% 2.91/1.41  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.91/1.41  tff('#skF_4', type, '#skF_4': $i).
% 2.91/1.41  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.91/1.41  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.91/1.41  
% 2.91/1.42  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.91/1.42  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.91/1.42  tff(f_37, axiom, (![A, B]: (k5_xboole_0(A, B) = k2_xboole_0(k4_xboole_0(A, B), k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d6_xboole_0)).
% 2.91/1.42  tff(f_42, negated_conjecture, ~(![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.91/1.42  tff(c_22, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.91/1.42  tff(c_60, plain, (![A_27, B_28, C_29]: (r2_hidden('#skF_1'(A_27, B_28, C_29), A_27) | r2_hidden('#skF_2'(A_27, B_28, C_29), C_29) | k4_xboole_0(A_27, B_28)=C_29)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.91/1.42  tff(c_14, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.91/1.42  tff(c_81, plain, (![A_27, B_28]: (r2_hidden('#skF_2'(A_27, B_28, A_27), A_27) | k4_xboole_0(A_27, B_28)=A_27)), inference(resolution, [status(thm)], [c_60, c_14])).
% 2.91/1.42  tff(c_444, plain, (![A_65, B_66, C_67]: (r2_hidden('#skF_1'(A_65, B_66, C_67), A_65) | r2_hidden('#skF_2'(A_65, B_66, C_67), B_66) | ~r2_hidden('#skF_2'(A_65, B_66, C_67), A_65) | k4_xboole_0(A_65, B_66)=C_67)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.91/1.42  tff(c_8, plain, (![A_1, B_2, C_3]: (~r2_hidden('#skF_1'(A_1, B_2, C_3), C_3) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.91/1.42  tff(c_773, plain, (![A_76, B_77]: (r2_hidden('#skF_2'(A_76, B_77, A_76), B_77) | ~r2_hidden('#skF_2'(A_76, B_77, A_76), A_76) | k4_xboole_0(A_76, B_77)=A_76)), inference(resolution, [status(thm)], [c_444, c_8])).
% 2.91/1.42  tff(c_787, plain, (![A_78, B_79]: (r2_hidden('#skF_2'(A_78, B_79, A_78), B_79) | k4_xboole_0(A_78, B_79)=A_78)), inference(resolution, [status(thm)], [c_81, c_773])).
% 2.91/1.42  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.91/1.42  tff(c_826, plain, (![A_84, A_85, B_86]: (~r2_hidden('#skF_2'(A_84, k4_xboole_0(A_85, B_86), A_84), B_86) | k4_xboole_0(A_84, k4_xboole_0(A_85, B_86))=A_84)), inference(resolution, [status(thm)], [c_787, c_4])).
% 2.91/1.42  tff(c_850, plain, (![A_87, A_88]: (k4_xboole_0(A_87, k4_xboole_0(A_88, A_87))=A_87)), inference(resolution, [status(thm)], [c_81, c_826])).
% 2.91/1.42  tff(c_20, plain, (![A_7, B_8]: (k2_xboole_0(k4_xboole_0(A_7, B_8), k4_xboole_0(B_8, A_7))=k5_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.91/1.42  tff(c_873, plain, (![A_87, A_88]: (k2_xboole_0(A_87, k4_xboole_0(k4_xboole_0(A_88, A_87), A_87))=k5_xboole_0(A_87, k4_xboole_0(A_88, A_87)))), inference(superposition, [status(thm), theory('equality')], [c_850, c_20])).
% 2.91/1.42  tff(c_903, plain, (![A_87, A_88]: (k5_xboole_0(A_87, k4_xboole_0(A_88, A_87))=k2_xboole_0(A_87, A_88))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_22, c_873])).
% 2.91/1.42  tff(c_24, plain, (k5_xboole_0('#skF_3', k4_xboole_0('#skF_4', '#skF_3'))!=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.91/1.42  tff(c_1202, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_903, c_24])).
% 2.91/1.42  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.91/1.42  
% 2.91/1.42  Inference rules
% 2.91/1.42  ----------------------
% 2.91/1.42  #Ref     : 0
% 2.91/1.42  #Sup     : 316
% 2.91/1.42  #Fact    : 0
% 2.91/1.42  #Define  : 0
% 2.91/1.42  #Split   : 0
% 2.91/1.42  #Chain   : 0
% 2.91/1.42  #Close   : 0
% 2.91/1.42  
% 2.91/1.42  Ordering : KBO
% 2.91/1.42  
% 2.91/1.42  Simplification rules
% 2.91/1.42  ----------------------
% 2.91/1.42  #Subsume      : 136
% 2.91/1.42  #Demod        : 86
% 2.91/1.42  #Tautology    : 77
% 2.91/1.42  #SimpNegUnit  : 0
% 2.91/1.42  #BackRed      : 1
% 2.91/1.42  
% 2.91/1.42  #Partial instantiations: 0
% 2.91/1.42  #Strategies tried      : 1
% 2.91/1.42  
% 2.91/1.42  Timing (in seconds)
% 2.91/1.42  ----------------------
% 2.91/1.43  Preprocessing        : 0.25
% 2.91/1.43  Parsing              : 0.14
% 2.91/1.43  CNF conversion       : 0.02
% 2.91/1.43  Main loop            : 0.42
% 2.91/1.43  Inferencing          : 0.16
% 2.91/1.43  Reduction            : 0.12
% 2.91/1.43  Demodulation         : 0.10
% 2.91/1.43  BG Simplification    : 0.02
% 2.91/1.43  Subsumption          : 0.09
% 2.91/1.43  Abstraction          : 0.03
% 2.91/1.43  MUC search           : 0.00
% 2.91/1.43  Cooper               : 0.00
% 2.91/1.43  Total                : 0.70
% 2.91/1.43  Index Insertion      : 0.00
% 2.91/1.43  Index Deletion       : 0.00
% 2.91/1.43  Index Matching       : 0.00
% 2.91/1.43  BG Taut test         : 0.00
%------------------------------------------------------------------------------

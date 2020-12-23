%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:12 EST 2020

% Result     : Theorem 6.18s
% Output     : CNFRefutation 6.29s
% Verified   : 
% Statistics : Number of formulae       :   42 (  66 expanded)
%              Number of leaves         :   22 (  32 expanded)
%              Depth                    :    8
%              Number of atoms          :   36 (  69 expanded)
%              Number of equality atoms :   24 (  45 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => k3_xboole_0(A,k2_xboole_0(B,C)) = k3_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t78_xboole_1)).

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

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_24,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_156,plain,(
    ! [A_30,B_31,C_32] :
      ( ~ r1_xboole_0(A_30,B_31)
      | ~ r2_hidden(C_32,k3_xboole_0(A_30,B_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_307,plain,(
    ! [A_43,B_44] :
      ( ~ r1_xboole_0(A_43,B_44)
      | k3_xboole_0(A_43,B_44) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_156])).

tff(c_311,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_24,c_307])).

tff(c_20,plain,(
    ! [A_19,B_20] : k2_xboole_0(k3_xboole_0(A_19,B_20),k4_xboole_0(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_318,plain,(
    k2_xboole_0(k1_xboole_0,k4_xboole_0('#skF_3','#skF_4')) = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_311,c_20])).

tff(c_10,plain,(
    ! [A_10] : k3_xboole_0(A_10,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_14,plain,(
    ! [A_13] : k4_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_75,plain,(
    ! [A_26,B_27] : k2_xboole_0(k3_xboole_0(A_26,B_27),k4_xboole_0(A_26,B_27)) = A_26 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_84,plain,(
    ! [A_13] : k2_xboole_0(k3_xboole_0(A_13,k1_xboole_0),A_13) = A_13 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_75])).

tff(c_90,plain,(
    ! [A_13] : k2_xboole_0(k1_xboole_0,A_13) = A_13 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_84])).

tff(c_536,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_318,c_90])).

tff(c_18,plain,(
    ! [A_17,B_18] : k4_xboole_0(A_17,k4_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_324,plain,(
    ! [A_45,B_46,C_47] : k4_xboole_0(k4_xboole_0(A_45,B_46),C_47) = k4_xboole_0(A_45,k2_xboole_0(B_46,C_47)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_9750,plain,(
    ! [A_187,B_188,C_189] : k4_xboole_0(k4_xboole_0(A_187,B_188),k4_xboole_0(A_187,k2_xboole_0(B_188,C_189))) = k3_xboole_0(k4_xboole_0(A_187,B_188),C_189) ),
    inference(superposition,[status(thm),theory(equality)],[c_324,c_18])).

tff(c_9991,plain,(
    ! [C_189] : k4_xboole_0('#skF_3',k4_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_189))) = k3_xboole_0(k4_xboole_0('#skF_3','#skF_4'),C_189) ),
    inference(superposition,[status(thm),theory(equality)],[c_536,c_9750])).

tff(c_10104,plain,(
    ! [C_189] : k3_xboole_0('#skF_3',k2_xboole_0('#skF_4',C_189)) = k3_xboole_0('#skF_3',C_189) ),
    inference(demodulation,[status(thm),theory(equality)],[c_536,c_18,c_9991])).

tff(c_22,plain,(
    k3_xboole_0('#skF_3',k2_xboole_0('#skF_4','#skF_5')) != k3_xboole_0('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10221,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10104,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n011.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:50:42 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.18/2.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.18/2.44  
% 6.18/2.44  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.29/2.44  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 6.29/2.44  
% 6.29/2.44  %Foreground sorts:
% 6.29/2.44  
% 6.29/2.44  
% 6.29/2.44  %Background operators:
% 6.29/2.44  
% 6.29/2.44  
% 6.29/2.44  %Foreground operators:
% 6.29/2.44  tff('#skF_2', type, '#skF_2': $i > $i).
% 6.29/2.44  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.29/2.44  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.29/2.44  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.29/2.44  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.29/2.44  tff('#skF_5', type, '#skF_5': $i).
% 6.29/2.44  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 6.29/2.44  tff('#skF_3', type, '#skF_3': $i).
% 6.29/2.44  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.29/2.44  tff('#skF_4', type, '#skF_4': $i).
% 6.29/2.44  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.29/2.44  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.29/2.44  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.29/2.44  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.29/2.44  
% 6.29/2.45  tff(f_66, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => (k3_xboole_0(A, k2_xboole_0(B, C)) = k3_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t78_xboole_1)).
% 6.29/2.45  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 6.29/2.45  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.29/2.45  tff(f_61, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 6.29/2.45  tff(f_51, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 6.29/2.45  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 6.29/2.45  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 6.29/2.45  tff(f_57, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 6.29/2.45  tff(c_24, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.29/2.45  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 6.29/2.45  tff(c_156, plain, (![A_30, B_31, C_32]: (~r1_xboole_0(A_30, B_31) | ~r2_hidden(C_32, k3_xboole_0(A_30, B_31)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 6.29/2.45  tff(c_307, plain, (![A_43, B_44]: (~r1_xboole_0(A_43, B_44) | k3_xboole_0(A_43, B_44)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_156])).
% 6.29/2.45  tff(c_311, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_24, c_307])).
% 6.29/2.45  tff(c_20, plain, (![A_19, B_20]: (k2_xboole_0(k3_xboole_0(A_19, B_20), k4_xboole_0(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.29/2.45  tff(c_318, plain, (k2_xboole_0(k1_xboole_0, k4_xboole_0('#skF_3', '#skF_4'))='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_311, c_20])).
% 6.29/2.45  tff(c_10, plain, (![A_10]: (k3_xboole_0(A_10, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.29/2.45  tff(c_14, plain, (![A_13]: (k4_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_55])).
% 6.29/2.45  tff(c_75, plain, (![A_26, B_27]: (k2_xboole_0(k3_xboole_0(A_26, B_27), k4_xboole_0(A_26, B_27))=A_26)), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.29/2.45  tff(c_84, plain, (![A_13]: (k2_xboole_0(k3_xboole_0(A_13, k1_xboole_0), A_13)=A_13)), inference(superposition, [status(thm), theory('equality')], [c_14, c_75])).
% 6.29/2.45  tff(c_90, plain, (![A_13]: (k2_xboole_0(k1_xboole_0, A_13)=A_13)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_84])).
% 6.29/2.45  tff(c_536, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_318, c_90])).
% 6.29/2.45  tff(c_18, plain, (![A_17, B_18]: (k4_xboole_0(A_17, k4_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.29/2.45  tff(c_324, plain, (![A_45, B_46, C_47]: (k4_xboole_0(k4_xboole_0(A_45, B_46), C_47)=k4_xboole_0(A_45, k2_xboole_0(B_46, C_47)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.29/2.45  tff(c_9750, plain, (![A_187, B_188, C_189]: (k4_xboole_0(k4_xboole_0(A_187, B_188), k4_xboole_0(A_187, k2_xboole_0(B_188, C_189)))=k3_xboole_0(k4_xboole_0(A_187, B_188), C_189))), inference(superposition, [status(thm), theory('equality')], [c_324, c_18])).
% 6.29/2.45  tff(c_9991, plain, (![C_189]: (k4_xboole_0('#skF_3', k4_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_189)))=k3_xboole_0(k4_xboole_0('#skF_3', '#skF_4'), C_189))), inference(superposition, [status(thm), theory('equality')], [c_536, c_9750])).
% 6.29/2.45  tff(c_10104, plain, (![C_189]: (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', C_189))=k3_xboole_0('#skF_3', C_189))), inference(demodulation, [status(thm), theory('equality')], [c_536, c_18, c_9991])).
% 6.29/2.45  tff(c_22, plain, (k3_xboole_0('#skF_3', k2_xboole_0('#skF_4', '#skF_5'))!=k3_xboole_0('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_66])).
% 6.29/2.45  tff(c_10221, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10104, c_22])).
% 6.29/2.45  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.29/2.45  
% 6.29/2.45  Inference rules
% 6.29/2.45  ----------------------
% 6.29/2.45  #Ref     : 0
% 6.29/2.45  #Sup     : 2546
% 6.29/2.45  #Fact    : 0
% 6.29/2.45  #Define  : 0
% 6.29/2.45  #Split   : 1
% 6.29/2.45  #Chain   : 0
% 6.29/2.45  #Close   : 0
% 6.29/2.45  
% 6.29/2.45  Ordering : KBO
% 6.29/2.45  
% 6.29/2.45  Simplification rules
% 6.29/2.45  ----------------------
% 6.29/2.45  #Subsume      : 20
% 6.29/2.45  #Demod        : 2770
% 6.29/2.45  #Tautology    : 1601
% 6.29/2.45  #SimpNegUnit  : 9
% 6.29/2.45  #BackRed      : 6
% 6.29/2.45  
% 6.29/2.45  #Partial instantiations: 0
% 6.29/2.45  #Strategies tried      : 1
% 6.29/2.45  
% 6.29/2.45  Timing (in seconds)
% 6.29/2.45  ----------------------
% 6.29/2.45  Preprocessing        : 0.27
% 6.29/2.45  Parsing              : 0.16
% 6.29/2.45  CNF conversion       : 0.02
% 6.29/2.45  Main loop            : 1.42
% 6.29/2.45  Inferencing          : 0.36
% 6.29/2.45  Reduction            : 0.75
% 6.29/2.45  Demodulation         : 0.64
% 6.29/2.45  BG Simplification    : 0.04
% 6.29/2.45  Subsumption          : 0.19
% 6.29/2.45  Abstraction          : 0.06
% 6.29/2.46  MUC search           : 0.00
% 6.29/2.46  Cooper               : 0.00
% 6.29/2.46  Total                : 1.73
% 6.29/2.46  Index Insertion      : 0.00
% 6.29/2.46  Index Deletion       : 0.00
% 6.29/2.46  Index Matching       : 0.00
% 6.29/2.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------

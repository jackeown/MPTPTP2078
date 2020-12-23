%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:41 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   44 (  64 expanded)
%              Number of leaves         :   21 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  76 expanded)
%              Number of equality atoms :   26 (  47 expanded)
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

tff(f_66,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( k2_xboole_0(A,B) = k2_xboole_0(C,B)
          & r1_xboole_0(A,B)
          & r1_xboole_0(C,B) )
       => A = C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(c_18,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_10,plain,(
    ! [A_10] : k4_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_22,plain,(
    r1_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_207,plain,(
    ! [A_29,B_30,C_31] :
      ( ~ r1_xboole_0(A_29,B_30)
      | ~ r2_hidden(C_31,k3_xboole_0(A_29,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_307,plain,(
    ! [A_34,B_35] :
      ( ~ r1_xboole_0(A_34,B_35)
      | k3_xboole_0(A_34,B_35) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_207])).

tff(c_315,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_22,c_307])).

tff(c_14,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k3_xboole_0(A_13,B_14)) = k4_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_358,plain,(
    k4_xboole_0('#skF_3',k1_xboole_0) = k4_xboole_0('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_315,c_14])).

tff(c_365,plain,(
    k4_xboole_0('#skF_3','#skF_4') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_358])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_106,plain,(
    ! [A_25,B_26] : k4_xboole_0(k2_xboole_0(A_25,B_26),B_26) = k4_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_125,plain,(
    ! [B_2,A_1] : k4_xboole_0(k2_xboole_0(B_2,A_1),B_2) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_106])).

tff(c_20,plain,(
    r1_xboole_0('#skF_5','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_314,plain,(
    k3_xboole_0('#skF_5','#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_307])).

tff(c_334,plain,(
    k4_xboole_0('#skF_5',k1_xboole_0) = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_314,c_14])).

tff(c_340,plain,(
    k4_xboole_0('#skF_5','#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_334])).

tff(c_24,plain,(
    k2_xboole_0('#skF_5','#skF_4') = k2_xboole_0('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_25,plain,(
    k2_xboole_0('#skF_4','#skF_5') = k2_xboole_0('#skF_4','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_24])).

tff(c_431,plain,(
    ! [B_39,A_40] : k4_xboole_0(k2_xboole_0(B_39,A_40),B_39) = k4_xboole_0(A_40,B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_106])).

tff(c_461,plain,(
    k4_xboole_0(k2_xboole_0('#skF_4','#skF_3'),'#skF_4') = k4_xboole_0('#skF_5','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_431])).

tff(c_479,plain,(
    '#skF_5' = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_365,c_125,c_340,c_461])).

tff(c_481,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_479])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n009.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:05:26 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.97/1.30  
% 1.97/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.30  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_3 > #skF_4 > #skF_1
% 2.24/1.30  
% 2.24/1.30  %Foreground sorts:
% 2.24/1.30  
% 2.24/1.30  
% 2.24/1.30  %Background operators:
% 2.24/1.30  
% 2.24/1.30  
% 2.24/1.30  %Foreground operators:
% 2.24/1.30  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.24/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.24/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.24/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.24/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.24/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.24/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.24/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.24/1.30  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.24/1.30  
% 2.24/1.31  tff(f_66, negated_conjecture, ~(![A, B, C]: ((((k2_xboole_0(A, B) = k2_xboole_0(C, B)) & r1_xboole_0(A, B)) & r1_xboole_0(C, B)) => (A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_xboole_1)).
% 2.24/1.31  tff(f_51, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 2.24/1.31  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.24/1.31  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.24/1.31  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.24/1.31  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.24/1.31  tff(f_53, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 2.24/1.31  tff(c_18, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.24/1.31  tff(c_10, plain, (![A_10]: (k4_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.24/1.31  tff(c_22, plain, (r1_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.24/1.31  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.24/1.31  tff(c_207, plain, (![A_29, B_30, C_31]: (~r1_xboole_0(A_29, B_30) | ~r2_hidden(C_31, k3_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.24/1.31  tff(c_307, plain, (![A_34, B_35]: (~r1_xboole_0(A_34, B_35) | k3_xboole_0(A_34, B_35)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_207])).
% 2.24/1.31  tff(c_315, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_22, c_307])).
% 2.24/1.31  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k3_xboole_0(A_13, B_14))=k4_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.24/1.31  tff(c_358, plain, (k4_xboole_0('#skF_3', k1_xboole_0)=k4_xboole_0('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_315, c_14])).
% 2.24/1.31  tff(c_365, plain, (k4_xboole_0('#skF_3', '#skF_4')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_358])).
% 2.24/1.31  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.24/1.31  tff(c_106, plain, (![A_25, B_26]: (k4_xboole_0(k2_xboole_0(A_25, B_26), B_26)=k4_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.24/1.31  tff(c_125, plain, (![B_2, A_1]: (k4_xboole_0(k2_xboole_0(B_2, A_1), B_2)=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_106])).
% 2.24/1.31  tff(c_20, plain, (r1_xboole_0('#skF_5', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.24/1.31  tff(c_314, plain, (k3_xboole_0('#skF_5', '#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_20, c_307])).
% 2.24/1.31  tff(c_334, plain, (k4_xboole_0('#skF_5', k1_xboole_0)=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_314, c_14])).
% 2.24/1.31  tff(c_340, plain, (k4_xboole_0('#skF_5', '#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_10, c_334])).
% 2.24/1.31  tff(c_24, plain, (k2_xboole_0('#skF_5', '#skF_4')=k2_xboole_0('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.24/1.31  tff(c_25, plain, (k2_xboole_0('#skF_4', '#skF_5')=k2_xboole_0('#skF_4', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_24])).
% 2.24/1.31  tff(c_431, plain, (![B_39, A_40]: (k4_xboole_0(k2_xboole_0(B_39, A_40), B_39)=k4_xboole_0(A_40, B_39))), inference(superposition, [status(thm), theory('equality')], [c_2, c_106])).
% 2.24/1.31  tff(c_461, plain, (k4_xboole_0(k2_xboole_0('#skF_4', '#skF_3'), '#skF_4')=k4_xboole_0('#skF_5', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_25, c_431])).
% 2.24/1.31  tff(c_479, plain, ('#skF_5'='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_365, c_125, c_340, c_461])).
% 2.24/1.31  tff(c_481, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_479])).
% 2.24/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.31  
% 2.24/1.31  Inference rules
% 2.24/1.31  ----------------------
% 2.24/1.31  #Ref     : 0
% 2.24/1.31  #Sup     : 117
% 2.24/1.31  #Fact    : 0
% 2.24/1.31  #Define  : 0
% 2.24/1.31  #Split   : 1
% 2.24/1.31  #Chain   : 0
% 2.24/1.31  #Close   : 0
% 2.24/1.31  
% 2.24/1.31  Ordering : KBO
% 2.24/1.31  
% 2.24/1.31  Simplification rules
% 2.24/1.31  ----------------------
% 2.24/1.31  #Subsume      : 2
% 2.24/1.31  #Demod        : 57
% 2.24/1.31  #Tautology    : 74
% 2.24/1.31  #SimpNegUnit  : 4
% 2.24/1.31  #BackRed      : 0
% 2.24/1.31  
% 2.24/1.31  #Partial instantiations: 0
% 2.24/1.31  #Strategies tried      : 1
% 2.24/1.31  
% 2.24/1.31  Timing (in seconds)
% 2.24/1.31  ----------------------
% 2.24/1.31  Preprocessing        : 0.31
% 2.24/1.31  Parsing              : 0.17
% 2.24/1.31  CNF conversion       : 0.02
% 2.24/1.31  Main loop            : 0.23
% 2.24/1.32  Inferencing          : 0.09
% 2.24/1.32  Reduction            : 0.09
% 2.24/1.32  Demodulation         : 0.07
% 2.24/1.32  BG Simplification    : 0.01
% 2.24/1.32  Subsumption          : 0.03
% 2.24/1.32  Abstraction          : 0.01
% 2.24/1.32  MUC search           : 0.00
% 2.24/1.32  Cooper               : 0.00
% 2.24/1.32  Total                : 0.57
% 2.24/1.32  Index Insertion      : 0.00
% 2.24/1.32  Index Deletion       : 0.00
% 2.24/1.32  Index Matching       : 0.00
% 2.24/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------

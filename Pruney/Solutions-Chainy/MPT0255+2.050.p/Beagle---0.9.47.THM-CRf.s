%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:45 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   41 (  93 expanded)
%              Number of leaves         :   20 (  40 expanded)
%              Depth                    :    8
%              Number of atoms          :   30 (  94 expanded)
%              Number of equality atoms :   21 (  59 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_43,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_39,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(c_16,plain,(
    ! [A_10,B_11] : k2_xboole_0(k1_tarski(A_10),k1_tarski(B_11)) = k2_tarski(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12,plain,(
    ! [A_7] : r1_tarski(k1_xboole_0,A_7) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_192,plain,(
    ! [A_37,B_38] :
      ( k2_xboole_0(A_37,B_38) = B_38
      | ~ r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_281,plain,(
    ! [A_44] : k2_xboole_0(k1_xboole_0,A_44) = A_44 ),
    inference(resolution,[status(thm)],[c_12,c_192])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_298,plain,(
    ! [A_44] : k2_xboole_0(A_44,k1_xboole_0) = A_44 ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_2])).

tff(c_26,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_48,plain,(
    ! [B_26,A_27] : k2_xboole_0(B_26,A_27) = k2_xboole_0(A_27,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_107,plain,(
    ! [A_28,B_29] : r1_tarski(A_28,k2_xboole_0(B_29,A_28)) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_14])).

tff(c_116,plain,(
    r1_tarski('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_107])).

tff(c_215,plain,(
    k2_xboole_0('#skF_3',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_116,c_192])).

tff(c_326,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_298,c_215])).

tff(c_24,plain,(
    ! [A_17,B_18] : k2_xboole_0(k1_tarski(A_17),B_18) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_605,plain,(
    ! [A_54,B_55] : k2_xboole_0(k1_tarski(A_54),B_55) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_24])).

tff(c_607,plain,(
    ! [A_10,B_11] : k2_tarski(A_10,B_11) != '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_605])).

tff(c_393,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_26])).

tff(c_301,plain,(
    ! [A_44] : k2_xboole_0(A_44,k1_xboole_0) = A_44 ),
    inference(superposition,[status(thm),theory(equality)],[c_281,c_2])).

tff(c_423,plain,(
    ! [A_44] : k2_xboole_0(A_44,'#skF_3') = A_44 ),
    inference(demodulation,[status(thm),theory(equality)],[c_326,c_301])).

tff(c_470,plain,(
    k2_tarski('#skF_1','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_393,c_423])).

tff(c_625,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_607,c_470])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n008.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 13:45:30 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.33  
% 2.19/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.34  %$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.19/1.34  
% 2.19/1.34  %Foreground sorts:
% 2.19/1.34  
% 2.19/1.34  
% 2.19/1.34  %Background operators:
% 2.19/1.34  
% 2.19/1.34  
% 2.19/1.34  %Foreground operators:
% 2.19/1.34  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.34  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.34  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.19/1.34  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.34  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.34  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.34  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.34  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.34  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.34  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.34  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.19/1.34  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.34  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.34  
% 2.19/1.34  tff(f_43, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 2.19/1.34  tff(f_39, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.19/1.34  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.19/1.34  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.19/1.34  tff(f_56, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.19/1.34  tff(f_41, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.19/1.34  tff(f_52, axiom, (![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.19/1.34  tff(c_16, plain, (![A_10, B_11]: (k2_xboole_0(k1_tarski(A_10), k1_tarski(B_11))=k2_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.19/1.34  tff(c_12, plain, (![A_7]: (r1_tarski(k1_xboole_0, A_7))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.19/1.34  tff(c_192, plain, (![A_37, B_38]: (k2_xboole_0(A_37, B_38)=B_38 | ~r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.34  tff(c_281, plain, (![A_44]: (k2_xboole_0(k1_xboole_0, A_44)=A_44)), inference(resolution, [status(thm)], [c_12, c_192])).
% 2.19/1.34  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.19/1.34  tff(c_298, plain, (![A_44]: (k2_xboole_0(A_44, k1_xboole_0)=A_44)), inference(superposition, [status(thm), theory('equality')], [c_281, c_2])).
% 2.19/1.34  tff(c_26, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.19/1.34  tff(c_48, plain, (![B_26, A_27]: (k2_xboole_0(B_26, A_27)=k2_xboole_0(A_27, B_26))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.19/1.34  tff(c_14, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.19/1.34  tff(c_107, plain, (![A_28, B_29]: (r1_tarski(A_28, k2_xboole_0(B_29, A_28)))), inference(superposition, [status(thm), theory('equality')], [c_48, c_14])).
% 2.19/1.34  tff(c_116, plain, (r1_tarski('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_107])).
% 2.19/1.34  tff(c_215, plain, (k2_xboole_0('#skF_3', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_116, c_192])).
% 2.19/1.34  tff(c_326, plain, (k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_298, c_215])).
% 2.19/1.34  tff(c_24, plain, (![A_17, B_18]: (k2_xboole_0(k1_tarski(A_17), B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 2.19/1.34  tff(c_605, plain, (![A_54, B_55]: (k2_xboole_0(k1_tarski(A_54), B_55)!='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_326, c_24])).
% 2.19/1.34  tff(c_607, plain, (![A_10, B_11]: (k2_tarski(A_10, B_11)!='#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_16, c_605])).
% 2.19/1.34  tff(c_393, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_326, c_26])).
% 2.19/1.34  tff(c_301, plain, (![A_44]: (k2_xboole_0(A_44, k1_xboole_0)=A_44)), inference(superposition, [status(thm), theory('equality')], [c_281, c_2])).
% 2.19/1.34  tff(c_423, plain, (![A_44]: (k2_xboole_0(A_44, '#skF_3')=A_44)), inference(demodulation, [status(thm), theory('equality')], [c_326, c_301])).
% 2.19/1.34  tff(c_470, plain, (k2_tarski('#skF_1', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_393, c_423])).
% 2.19/1.34  tff(c_625, plain, $false, inference(negUnitSimplification, [status(thm)], [c_607, c_470])).
% 2.19/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.34  
% 2.19/1.34  Inference rules
% 2.19/1.34  ----------------------
% 2.19/1.34  #Ref     : 0
% 2.19/1.34  #Sup     : 144
% 2.19/1.34  #Fact    : 0
% 2.19/1.34  #Define  : 0
% 2.19/1.34  #Split   : 0
% 2.19/1.34  #Chain   : 0
% 2.19/1.34  #Close   : 0
% 2.19/1.34  
% 2.19/1.34  Ordering : KBO
% 2.19/1.34  
% 2.19/1.34  Simplification rules
% 2.19/1.34  ----------------------
% 2.19/1.35  #Subsume      : 12
% 2.19/1.35  #Demod        : 67
% 2.19/1.35  #Tautology    : 102
% 2.19/1.35  #SimpNegUnit  : 1
% 2.19/1.35  #BackRed      : 16
% 2.19/1.35  
% 2.19/1.35  #Partial instantiations: 0
% 2.19/1.35  #Strategies tried      : 1
% 2.19/1.35  
% 2.19/1.35  Timing (in seconds)
% 2.19/1.35  ----------------------
% 2.19/1.35  Preprocessing        : 0.31
% 2.19/1.35  Parsing              : 0.16
% 2.19/1.35  CNF conversion       : 0.02
% 2.19/1.35  Main loop            : 0.23
% 2.19/1.35  Inferencing          : 0.08
% 2.19/1.35  Reduction            : 0.09
% 2.19/1.35  Demodulation         : 0.07
% 2.19/1.35  BG Simplification    : 0.01
% 2.19/1.35  Subsumption          : 0.03
% 2.19/1.35  Abstraction          : 0.01
% 2.19/1.35  MUC search           : 0.00
% 2.19/1.35  Cooper               : 0.00
% 2.19/1.35  Total                : 0.56
% 2.19/1.35  Index Insertion      : 0.00
% 2.19/1.35  Index Deletion       : 0.00
% 2.19/1.35  Index Matching       : 0.00
% 2.19/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:52 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   18 (  20 expanded)
%              Depth                    :    7
%              Number of atoms          :   29 (  33 expanded)
%              Number of equality atoms :   20 (  24 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C] :
        ( A != B
       => k4_xboole_0(k2_xboole_0(C,k1_tarski(A)),k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C,k1_tarski(B)),k1_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => k4_xboole_0(k2_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t141_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] : k4_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(k4_xboole_0(A,C),k4_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t42_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_24,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : k4_xboole_0(k2_xboole_0(A_3,B_4),B_4) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [B_14,A_13] :
      ( k4_xboole_0(k2_xboole_0(B_14,k1_tarski(A_13)),k1_tarski(A_13)) = B_14
      | r2_hidden(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_25,plain,(
    ! [B_14,A_13] :
      ( k4_xboole_0(B_14,k1_tarski(A_13)) = B_14
      | r2_hidden(A_13,B_14) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_20])).

tff(c_139,plain,(
    ! [A_28,C_29,B_30] : k2_xboole_0(k4_xboole_0(A_28,C_29),k4_xboole_0(B_30,C_29)) = k4_xboole_0(k2_xboole_0(A_28,B_30),C_29) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1375,plain,(
    ! [A_71,B_72,A_73] :
      ( k4_xboole_0(k2_xboole_0(A_71,B_72),k1_tarski(A_73)) = k2_xboole_0(k4_xboole_0(A_71,k1_tarski(A_73)),B_72)
      | r2_hidden(A_73,B_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_25,c_139])).

tff(c_22,plain,(
    k4_xboole_0(k2_xboole_0('#skF_5',k1_tarski('#skF_3')),k1_tarski('#skF_4')) != k2_xboole_0(k4_xboole_0('#skF_5',k1_tarski('#skF_4')),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    k4_xboole_0(k2_xboole_0('#skF_5',k1_tarski('#skF_3')),k1_tarski('#skF_4')) != k2_xboole_0(k1_tarski('#skF_3'),k4_xboole_0('#skF_5',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_1431,plain,
    ( k2_xboole_0(k4_xboole_0('#skF_5',k1_tarski('#skF_4')),k1_tarski('#skF_3')) != k2_xboole_0(k1_tarski('#skF_3'),k4_xboole_0('#skF_5',k1_tarski('#skF_4')))
    | r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1375,c_26])).

tff(c_1516,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1431])).

tff(c_8,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_1526,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_1516,c_8])).

tff(c_1530,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_1526])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n023.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 13:19:51 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.54  
% 3.46/1.54  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.54  %$ r2_hidden > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 3.46/1.54  
% 3.46/1.54  %Foreground sorts:
% 3.46/1.54  
% 3.46/1.54  
% 3.46/1.54  %Background operators:
% 3.46/1.54  
% 3.46/1.54  
% 3.46/1.54  %Foreground operators:
% 3.46/1.54  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.54  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.46/1.54  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.46/1.54  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.46/1.54  tff('#skF_5', type, '#skF_5': $i).
% 3.46/1.54  tff('#skF_3', type, '#skF_3': $i).
% 3.46/1.54  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.54  tff('#skF_4', type, '#skF_4': $i).
% 3.46/1.54  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.54  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 3.46/1.54  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.46/1.54  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.46/1.54  
% 3.46/1.55  tff(f_49, negated_conjecture, ~(![A, B, C]: (~(A = B) => (k4_xboole_0(k2_xboole_0(C, k1_tarski(A)), k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C, k1_tarski(B)), k1_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_zfmisc_1)).
% 3.46/1.55  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.46/1.55  tff(f_29, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t40_xboole_1)).
% 3.46/1.55  tff(f_43, axiom, (![A, B]: (~r2_hidden(A, B) => (k4_xboole_0(k2_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t141_zfmisc_1)).
% 3.46/1.55  tff(f_31, axiom, (![A, B, C]: (k4_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t42_xboole_1)).
% 3.46/1.55  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 3.46/1.55  tff(c_24, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.46/1.55  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.46/1.55  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(k2_xboole_0(A_3, B_4), B_4)=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.46/1.55  tff(c_20, plain, (![B_14, A_13]: (k4_xboole_0(k2_xboole_0(B_14, k1_tarski(A_13)), k1_tarski(A_13))=B_14 | r2_hidden(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.46/1.55  tff(c_25, plain, (![B_14, A_13]: (k4_xboole_0(B_14, k1_tarski(A_13))=B_14 | r2_hidden(A_13, B_14))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_20])).
% 3.46/1.55  tff(c_139, plain, (![A_28, C_29, B_30]: (k2_xboole_0(k4_xboole_0(A_28, C_29), k4_xboole_0(B_30, C_29))=k4_xboole_0(k2_xboole_0(A_28, B_30), C_29))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.46/1.55  tff(c_1375, plain, (![A_71, B_72, A_73]: (k4_xboole_0(k2_xboole_0(A_71, B_72), k1_tarski(A_73))=k2_xboole_0(k4_xboole_0(A_71, k1_tarski(A_73)), B_72) | r2_hidden(A_73, B_72))), inference(superposition, [status(thm), theory('equality')], [c_25, c_139])).
% 3.46/1.55  tff(c_22, plain, (k4_xboole_0(k2_xboole_0('#skF_5', k1_tarski('#skF_3')), k1_tarski('#skF_4'))!=k2_xboole_0(k4_xboole_0('#skF_5', k1_tarski('#skF_4')), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.46/1.55  tff(c_26, plain, (k4_xboole_0(k2_xboole_0('#skF_5', k1_tarski('#skF_3')), k1_tarski('#skF_4'))!=k2_xboole_0(k1_tarski('#skF_3'), k4_xboole_0('#skF_5', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 3.46/1.55  tff(c_1431, plain, (k2_xboole_0(k4_xboole_0('#skF_5', k1_tarski('#skF_4')), k1_tarski('#skF_3'))!=k2_xboole_0(k1_tarski('#skF_3'), k4_xboole_0('#skF_5', k1_tarski('#skF_4'))) | r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_1375, c_26])).
% 3.46/1.55  tff(c_1516, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1431])).
% 3.46/1.55  tff(c_8, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 3.46/1.55  tff(c_1526, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_1516, c_8])).
% 3.46/1.55  tff(c_1530, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_1526])).
% 3.46/1.55  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.46/1.55  
% 3.46/1.55  Inference rules
% 3.46/1.55  ----------------------
% 3.46/1.55  #Ref     : 0
% 3.46/1.55  #Sup     : 356
% 3.46/1.55  #Fact    : 0
% 3.46/1.55  #Define  : 0
% 3.46/1.55  #Split   : 1
% 3.46/1.55  #Chain   : 0
% 3.46/1.55  #Close   : 0
% 3.46/1.55  
% 3.46/1.55  Ordering : KBO
% 3.46/1.55  
% 3.46/1.55  Simplification rules
% 3.46/1.55  ----------------------
% 3.46/1.55  #Subsume      : 30
% 3.46/1.55  #Demod        : 261
% 3.46/1.55  #Tautology    : 179
% 3.46/1.55  #SimpNegUnit  : 1
% 3.46/1.55  #BackRed      : 0
% 3.46/1.55  
% 3.46/1.55  #Partial instantiations: 0
% 3.46/1.55  #Strategies tried      : 1
% 3.46/1.55  
% 3.46/1.55  Timing (in seconds)
% 3.46/1.55  ----------------------
% 3.46/1.55  Preprocessing        : 0.28
% 3.46/1.55  Parsing              : 0.14
% 3.46/1.55  CNF conversion       : 0.02
% 3.46/1.55  Main loop            : 0.53
% 3.46/1.55  Inferencing          : 0.17
% 3.46/1.55  Reduction            : 0.24
% 3.46/1.55  Demodulation         : 0.20
% 3.46/1.55  BG Simplification    : 0.02
% 3.46/1.55  Subsumption          : 0.07
% 3.46/1.55  Abstraction          : 0.03
% 3.46/1.55  MUC search           : 0.00
% 3.46/1.56  Cooper               : 0.00
% 3.46/1.56  Total                : 0.83
% 3.46/1.56  Index Insertion      : 0.00
% 3.46/1.56  Index Deletion       : 0.00
% 3.46/1.56  Index Matching       : 0.00
% 3.46/1.56  BG Taut test         : 0.00
%------------------------------------------------------------------------------

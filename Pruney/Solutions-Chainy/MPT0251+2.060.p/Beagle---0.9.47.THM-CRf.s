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
% DateTime   : Thu Dec  3 09:50:54 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   35 (  45 expanded)
%              Number of leaves         :   19 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  44 expanded)
%              Number of equality atoms :   16 (  26 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_39,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_22,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_5] : k2_tarski(A_5,A_5) = k1_tarski(A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_201,plain,(
    ! [A_41,B_42,C_43] :
      ( r1_tarski(k2_tarski(A_41,B_42),C_43)
      | ~ r2_hidden(B_42,C_43)
      | ~ r2_hidden(A_41,C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_223,plain,(
    ! [A_44,C_45] :
      ( r1_tarski(k1_tarski(A_44),C_45)
      | ~ r2_hidden(A_44,C_45)
      | ~ r2_hidden(A_44,C_45) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_201])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k2_xboole_0(A_1,B_2) = B_2
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_232,plain,(
    ! [A_46,C_47] :
      ( k2_xboole_0(k1_tarski(A_46),C_47) = C_47
      | ~ r2_hidden(A_46,C_47) ) ),
    inference(resolution,[status(thm)],[c_223,c_2])).

tff(c_4,plain,(
    ! [B_4,A_3] : k2_tarski(B_4,A_3) = k2_tarski(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [A_23,B_24] : k3_tarski(k2_tarski(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_110,plain,(
    ! [A_26,B_27] : k3_tarski(k2_tarski(A_26,B_27)) = k2_xboole_0(B_27,A_26) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_75])).

tff(c_12,plain,(
    ! [A_11,B_12] : k3_tarski(k2_tarski(A_11,B_12)) = k2_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_116,plain,(
    ! [B_27,A_26] : k2_xboole_0(B_27,A_26) = k2_xboole_0(A_26,B_27) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_12])).

tff(c_263,plain,(
    ! [C_48,A_49] :
      ( k2_xboole_0(C_48,k1_tarski(A_49)) = C_48
      | ~ r2_hidden(A_49,C_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_232,c_116])).

tff(c_20,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_146,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_20])).

tff(c_273,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_263,c_146])).

tff(c_307,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_273])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n008.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:42:15 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.17  
% 1.89/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.17  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 1.89/1.17  
% 1.89/1.17  %Foreground sorts:
% 1.89/1.17  
% 1.89/1.17  
% 1.89/1.17  %Background operators:
% 1.89/1.17  
% 1.89/1.17  
% 1.89/1.17  %Foreground operators:
% 1.89/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.89/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.89/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.89/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.17  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.89/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.89/1.17  
% 1.89/1.18  tff(f_50, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 1.89/1.18  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.89/1.18  tff(f_45, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.89/1.18  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.89/1.18  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.89/1.18  tff(f_39, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.89/1.18  tff(c_22, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.89/1.18  tff(c_6, plain, (![A_5]: (k2_tarski(A_5, A_5)=k1_tarski(A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.89/1.18  tff(c_201, plain, (![A_41, B_42, C_43]: (r1_tarski(k2_tarski(A_41, B_42), C_43) | ~r2_hidden(B_42, C_43) | ~r2_hidden(A_41, C_43))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.89/1.18  tff(c_223, plain, (![A_44, C_45]: (r1_tarski(k1_tarski(A_44), C_45) | ~r2_hidden(A_44, C_45) | ~r2_hidden(A_44, C_45))), inference(superposition, [status(thm), theory('equality')], [c_6, c_201])).
% 1.89/1.18  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, B_2)=B_2 | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.89/1.18  tff(c_232, plain, (![A_46, C_47]: (k2_xboole_0(k1_tarski(A_46), C_47)=C_47 | ~r2_hidden(A_46, C_47))), inference(resolution, [status(thm)], [c_223, c_2])).
% 1.89/1.18  tff(c_4, plain, (![B_4, A_3]: (k2_tarski(B_4, A_3)=k2_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.18  tff(c_75, plain, (![A_23, B_24]: (k3_tarski(k2_tarski(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.89/1.18  tff(c_110, plain, (![A_26, B_27]: (k3_tarski(k2_tarski(A_26, B_27))=k2_xboole_0(B_27, A_26))), inference(superposition, [status(thm), theory('equality')], [c_4, c_75])).
% 1.89/1.18  tff(c_12, plain, (![A_11, B_12]: (k3_tarski(k2_tarski(A_11, B_12))=k2_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.89/1.18  tff(c_116, plain, (![B_27, A_26]: (k2_xboole_0(B_27, A_26)=k2_xboole_0(A_26, B_27))), inference(superposition, [status(thm), theory('equality')], [c_110, c_12])).
% 1.89/1.18  tff(c_263, plain, (![C_48, A_49]: (k2_xboole_0(C_48, k1_tarski(A_49))=C_48 | ~r2_hidden(A_49, C_48))), inference(superposition, [status(thm), theory('equality')], [c_232, c_116])).
% 1.89/1.18  tff(c_20, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.89/1.18  tff(c_146, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_116, c_20])).
% 1.89/1.18  tff(c_273, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_263, c_146])).
% 1.89/1.18  tff(c_307, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_273])).
% 1.89/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.18  
% 1.89/1.18  Inference rules
% 1.89/1.18  ----------------------
% 1.89/1.18  #Ref     : 0
% 1.89/1.18  #Sup     : 71
% 1.89/1.18  #Fact    : 0
% 1.89/1.18  #Define  : 0
% 1.89/1.18  #Split   : 0
% 1.89/1.18  #Chain   : 0
% 1.89/1.18  #Close   : 0
% 1.89/1.18  
% 1.89/1.18  Ordering : KBO
% 1.89/1.18  
% 1.89/1.18  Simplification rules
% 1.89/1.18  ----------------------
% 1.89/1.18  #Subsume      : 9
% 1.89/1.18  #Demod        : 5
% 1.89/1.18  #Tautology    : 39
% 1.89/1.18  #SimpNegUnit  : 0
% 1.89/1.18  #BackRed      : 1
% 1.89/1.18  
% 1.89/1.18  #Partial instantiations: 0
% 1.89/1.18  #Strategies tried      : 1
% 1.89/1.18  
% 1.89/1.18  Timing (in seconds)
% 1.89/1.18  ----------------------
% 1.89/1.19  Preprocessing        : 0.27
% 1.89/1.19  Parsing              : 0.15
% 1.89/1.19  CNF conversion       : 0.02
% 1.89/1.19  Main loop            : 0.16
% 1.89/1.19  Inferencing          : 0.07
% 1.89/1.19  Reduction            : 0.05
% 1.89/1.19  Demodulation         : 0.04
% 1.89/1.19  BG Simplification    : 0.01
% 1.89/1.19  Subsumption          : 0.02
% 1.89/1.19  Abstraction          : 0.01
% 1.89/1.19  MUC search           : 0.00
% 1.89/1.19  Cooper               : 0.00
% 1.89/1.19  Total                : 0.46
% 1.89/1.19  Index Insertion      : 0.00
% 1.89/1.19  Index Deletion       : 0.00
% 1.89/1.19  Index Matching       : 0.00
% 1.89/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:04 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   40 (  41 expanded)
%              Number of leaves         :   25 (  26 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  34 expanded)
%              Number of equality atoms :   16 (  17 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
       => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_54,axiom,(
    ! [A] : k2_enumset1(A,A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t82_enumset1)).

tff(f_48,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_50,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_100,plain,(
    ! [A_45,B_46,C_47] : k2_enumset1(A_45,A_45,B_46,C_47) = k1_enumset1(A_45,B_46,C_47) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_46,plain,(
    ! [A_24] : k2_enumset1(A_24,A_24,A_24,A_24) = k1_tarski(A_24) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_116,plain,(
    ! [C_48] : k1_enumset1(C_48,C_48,C_48) = k1_tarski(C_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_46])).

tff(c_40,plain,(
    ! [A_15,B_16] : k1_enumset1(A_15,A_15,B_16) = k2_tarski(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_132,plain,(
    ! [C_49] : k2_tarski(C_49,C_49) = k1_tarski(C_49) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_40])).

tff(c_24,plain,(
    ! [D_14,A_9] : r2_hidden(D_14,k2_tarski(A_9,D_14)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_138,plain,(
    ! [C_49] : r2_hidden(C_49,k1_tarski(C_49)) ),
    inference(superposition,[status(thm),theory(equality)],[c_132,c_24])).

tff(c_52,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_79,plain,(
    ! [A_43,B_44] : k4_xboole_0(A_43,k4_xboole_0(A_43,B_44)) = k3_xboole_0(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_165,plain,(
    ! [D_54,A_55,B_56] :
      ( r2_hidden(D_54,A_55)
      | ~ r2_hidden(D_54,k3_xboole_0(A_55,B_56)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_6])).

tff(c_169,plain,(
    ! [D_57] :
      ( r2_hidden(D_57,'#skF_5')
      | ~ r2_hidden(D_57,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_165])).

tff(c_173,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_138,c_169])).

tff(c_177,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_173])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n015.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:02:38 EST 2020
% 0.20/0.33  % CPUTime    : 
% 0.20/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.17  
% 1.76/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.17  %$ r2_hidden > k6_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.76/1.17  
% 1.76/1.17  %Foreground sorts:
% 1.76/1.17  
% 1.76/1.17  
% 1.76/1.17  %Background operators:
% 1.76/1.17  
% 1.76/1.17  
% 1.76/1.17  %Foreground operators:
% 1.76/1.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.76/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.76/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.76/1.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.76/1.17  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.76/1.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.76/1.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.76/1.17  tff('#skF_5', type, '#skF_5': $i).
% 1.76/1.17  tff('#skF_6', type, '#skF_6': $i).
% 1.76/1.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.76/1.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.76/1.17  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.76/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.17  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.76/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.76/1.17  
% 1.99/1.18  tff(f_61, negated_conjecture, ~(![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 1.99/1.18  tff(f_50, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 1.99/1.18  tff(f_54, axiom, (![A]: (k2_enumset1(A, A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t82_enumset1)).
% 1.99/1.18  tff(f_48, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.99/1.18  tff(f_46, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.99/1.18  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.99/1.18  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.99/1.18  tff(c_50, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.99/1.18  tff(c_100, plain, (![A_45, B_46, C_47]: (k2_enumset1(A_45, A_45, B_46, C_47)=k1_enumset1(A_45, B_46, C_47))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.99/1.18  tff(c_46, plain, (![A_24]: (k2_enumset1(A_24, A_24, A_24, A_24)=k1_tarski(A_24))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.99/1.18  tff(c_116, plain, (![C_48]: (k1_enumset1(C_48, C_48, C_48)=k1_tarski(C_48))), inference(superposition, [status(thm), theory('equality')], [c_100, c_46])).
% 1.99/1.18  tff(c_40, plain, (![A_15, B_16]: (k1_enumset1(A_15, A_15, B_16)=k2_tarski(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.99/1.18  tff(c_132, plain, (![C_49]: (k2_tarski(C_49, C_49)=k1_tarski(C_49))), inference(superposition, [status(thm), theory('equality')], [c_116, c_40])).
% 1.99/1.18  tff(c_24, plain, (![D_14, A_9]: (r2_hidden(D_14, k2_tarski(A_9, D_14)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.99/1.18  tff(c_138, plain, (![C_49]: (r2_hidden(C_49, k1_tarski(C_49)))), inference(superposition, [status(thm), theory('equality')], [c_132, c_24])).
% 1.99/1.18  tff(c_52, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.99/1.18  tff(c_79, plain, (![A_43, B_44]: (k4_xboole_0(A_43, k4_xboole_0(A_43, B_44))=k3_xboole_0(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.99/1.18  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.99/1.18  tff(c_165, plain, (![D_54, A_55, B_56]: (r2_hidden(D_54, A_55) | ~r2_hidden(D_54, k3_xboole_0(A_55, B_56)))), inference(superposition, [status(thm), theory('equality')], [c_79, c_6])).
% 1.99/1.18  tff(c_169, plain, (![D_57]: (r2_hidden(D_57, '#skF_5') | ~r2_hidden(D_57, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_165])).
% 1.99/1.18  tff(c_173, plain, (r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_138, c_169])).
% 1.99/1.18  tff(c_177, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_173])).
% 1.99/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.18  
% 1.99/1.18  Inference rules
% 1.99/1.18  ----------------------
% 1.99/1.18  #Ref     : 0
% 1.99/1.18  #Sup     : 29
% 1.99/1.18  #Fact    : 0
% 1.99/1.18  #Define  : 0
% 1.99/1.18  #Split   : 0
% 1.99/1.18  #Chain   : 0
% 1.99/1.18  #Close   : 0
% 1.99/1.18  
% 1.99/1.18  Ordering : KBO
% 1.99/1.18  
% 1.99/1.18  Simplification rules
% 1.99/1.18  ----------------------
% 1.99/1.18  #Subsume      : 0
% 1.99/1.18  #Demod        : 3
% 1.99/1.18  #Tautology    : 19
% 1.99/1.18  #SimpNegUnit  : 1
% 1.99/1.18  #BackRed      : 0
% 1.99/1.18  
% 1.99/1.18  #Partial instantiations: 0
% 1.99/1.18  #Strategies tried      : 1
% 1.99/1.18  
% 1.99/1.18  Timing (in seconds)
% 1.99/1.18  ----------------------
% 1.99/1.18  Preprocessing        : 0.32
% 1.99/1.18  Parsing              : 0.16
% 1.99/1.18  CNF conversion       : 0.03
% 1.99/1.19  Main loop            : 0.14
% 1.99/1.19  Inferencing          : 0.04
% 1.99/1.19  Reduction            : 0.05
% 1.99/1.19  Demodulation         : 0.04
% 1.99/1.19  BG Simplification    : 0.01
% 1.99/1.19  Subsumption          : 0.03
% 1.99/1.19  Abstraction          : 0.01
% 1.99/1.19  MUC search           : 0.00
% 1.99/1.19  Cooper               : 0.00
% 1.99/1.19  Total                : 0.48
% 1.99/1.19  Index Insertion      : 0.00
% 1.99/1.19  Index Deletion       : 0.00
% 1.99/1.19  Index Matching       : 0.00
% 1.99/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

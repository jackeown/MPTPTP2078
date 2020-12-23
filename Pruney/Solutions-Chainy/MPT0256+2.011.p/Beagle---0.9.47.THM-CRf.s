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
% DateTime   : Thu Dec  3 09:52:03 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   27 (  28 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    4
%              Number of atoms          :   23 (  25 expanded)
%              Number of equality atoms :    9 (  10 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k3_xboole_0 > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
       => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d4_xboole_0)).

tff(c_48,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_44,plain,(
    ! [A_14] : k1_enumset1(A_14,A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_64,plain,(
    ! [E_17,B_18,C_19] : r2_hidden(E_17,k1_enumset1(E_17,B_18,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_67,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_64])).

tff(c_50,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_88,plain,(
    ! [D_28,A_29,B_30] :
      ( r2_hidden(D_28,A_29)
      | ~ r2_hidden(D_28,k3_xboole_0(A_29,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_92,plain,(
    ! [D_31] :
      ( r2_hidden(D_31,'#skF_5')
      | ~ r2_hidden(D_31,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_88])).

tff(c_96,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_67,c_92])).

tff(c_100,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_48,c_96])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:46:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.16  
% 1.76/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.16  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k3_xboole_0 > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 1.76/1.16  
% 1.76/1.16  %Foreground sorts:
% 1.76/1.16  
% 1.76/1.16  
% 1.76/1.16  %Background operators:
% 1.76/1.16  
% 1.76/1.16  
% 1.76/1.16  %Foreground operators:
% 1.76/1.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.76/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.76/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.76/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.76/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.76/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.76/1.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.76/1.16  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 1.76/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.76/1.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 1.76/1.16  
% 1.76/1.16  tff(f_58, negated_conjecture, ~(![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 1.76/1.16  tff(f_51, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_enumset1)).
% 1.76/1.16  tff(f_49, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.76/1.16  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.76/1.16  tff(c_48, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.76/1.16  tff(c_44, plain, (![A_14]: (k1_enumset1(A_14, A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.76/1.16  tff(c_64, plain, (![E_17, B_18, C_19]: (r2_hidden(E_17, k1_enumset1(E_17, B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.76/1.16  tff(c_67, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_64])).
% 1.76/1.16  tff(c_50, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.76/1.16  tff(c_88, plain, (![D_28, A_29, B_30]: (r2_hidden(D_28, A_29) | ~r2_hidden(D_28, k3_xboole_0(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.76/1.16  tff(c_92, plain, (![D_31]: (r2_hidden(D_31, '#skF_5') | ~r2_hidden(D_31, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_50, c_88])).
% 1.76/1.16  tff(c_96, plain, (r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_67, c_92])).
% 1.76/1.16  tff(c_100, plain, $false, inference(negUnitSimplification, [status(thm)], [c_48, c_96])).
% 1.76/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.16  
% 1.76/1.16  Inference rules
% 1.76/1.16  ----------------------
% 1.76/1.17  #Ref     : 0
% 1.76/1.17  #Sup     : 11
% 1.76/1.17  #Fact    : 0
% 1.76/1.17  #Define  : 0
% 1.76/1.17  #Split   : 0
% 1.76/1.17  #Chain   : 0
% 1.76/1.17  #Close   : 0
% 1.76/1.17  
% 1.76/1.17  Ordering : KBO
% 1.76/1.17  
% 1.76/1.17  Simplification rules
% 1.76/1.17  ----------------------
% 1.76/1.17  #Subsume      : 0
% 1.76/1.17  #Demod        : 2
% 1.76/1.17  #Tautology    : 8
% 1.76/1.17  #SimpNegUnit  : 1
% 1.76/1.17  #BackRed      : 0
% 1.76/1.17  
% 1.76/1.17  #Partial instantiations: 0
% 1.76/1.17  #Strategies tried      : 1
% 1.76/1.17  
% 1.76/1.17  Timing (in seconds)
% 1.76/1.17  ----------------------
% 1.86/1.17  Preprocessing        : 0.29
% 1.86/1.17  Parsing              : 0.14
% 1.86/1.17  CNF conversion       : 0.02
% 1.86/1.17  Main loop            : 0.11
% 1.86/1.17  Inferencing          : 0.03
% 1.86/1.17  Reduction            : 0.04
% 1.86/1.17  Demodulation         : 0.03
% 1.86/1.17  BG Simplification    : 0.01
% 1.86/1.17  Subsumption          : 0.02
% 1.86/1.17  Abstraction          : 0.01
% 1.86/1.17  MUC search           : 0.00
% 1.86/1.17  Cooper               : 0.00
% 1.86/1.17  Total                : 0.42
% 1.86/1.17  Index Insertion      : 0.00
% 1.86/1.17  Index Deletion       : 0.00
% 1.86/1.17  Index Matching       : 0.00
% 1.86/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------

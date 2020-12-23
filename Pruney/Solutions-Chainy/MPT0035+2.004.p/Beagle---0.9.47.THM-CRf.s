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
% DateTime   : Thu Dec  3 09:42:40 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   27 (  29 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  41 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_49,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B)
        & ! [D] :
            ( ( r1_tarski(A,D)
              & r1_tarski(C,D) )
           => r1_tarski(B,D) ) )
     => B = k2_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_xboole_1)).

tff(f_42,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(c_14,plain,(
    k3_xboole_0('#skF_2','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_26,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_29,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_26])).

tff(c_6,plain,(
    ! [C_5,A_3,B_4] :
      ( r1_tarski(C_5,'#skF_1'(A_3,B_4,C_5))
      | k2_xboole_0(A_3,C_5) = B_4
      | ~ r1_tarski(C_5,B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_53,plain,(
    ! [B_21,A_22,C_23] :
      ( ~ r1_tarski(B_21,'#skF_1'(A_22,B_21,C_23))
      | k2_xboole_0(A_22,C_23) = B_21
      | ~ r1_tarski(C_23,B_21)
      | ~ r1_tarski(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_57,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(B_4,B_4)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(resolution,[status(thm)],[c_6,c_53])).

tff(c_69,plain,(
    ! [A_27,B_28] :
      ( k2_xboole_0(A_27,B_28) = B_28
      | ~ r1_tarski(A_27,B_28) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_29,c_57])).

tff(c_90,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_16,c_69])).

tff(c_10,plain,(
    ! [A_7,B_8] : k3_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_94,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_90,c_10])).

tff(c_101,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_94])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 11:53:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.14  
% 1.62/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.15  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_1 > #skF_2 > #skF_3
% 1.62/1.15  
% 1.62/1.15  %Foreground sorts:
% 1.62/1.15  
% 1.62/1.15  
% 1.62/1.15  %Background operators:
% 1.62/1.15  
% 1.62/1.15  
% 1.62/1.15  %Foreground operators:
% 1.62/1.15  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.62/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.62/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.62/1.15  
% 1.62/1.15  tff(f_49, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.62/1.15  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.62/1.15  tff(f_44, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.62/1.15  tff(f_40, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(C, B)) & (![D]: ((r1_tarski(A, D) & r1_tarski(C, D)) => r1_tarski(B, D)))) => (B = k2_xboole_0(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_xboole_1)).
% 1.62/1.15  tff(f_42, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.62/1.15  tff(c_14, plain, (k3_xboole_0('#skF_2', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.62/1.15  tff(c_16, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.62/1.15  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.15  tff(c_26, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.62/1.15  tff(c_29, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_26])).
% 1.62/1.15  tff(c_6, plain, (![C_5, A_3, B_4]: (r1_tarski(C_5, '#skF_1'(A_3, B_4, C_5)) | k2_xboole_0(A_3, C_5)=B_4 | ~r1_tarski(C_5, B_4) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.62/1.15  tff(c_53, plain, (![B_21, A_22, C_23]: (~r1_tarski(B_21, '#skF_1'(A_22, B_21, C_23)) | k2_xboole_0(A_22, C_23)=B_21 | ~r1_tarski(C_23, B_21) | ~r1_tarski(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.62/1.15  tff(c_57, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(B_4, B_4) | ~r1_tarski(A_3, B_4))), inference(resolution, [status(thm)], [c_6, c_53])).
% 1.62/1.15  tff(c_69, plain, (![A_27, B_28]: (k2_xboole_0(A_27, B_28)=B_28 | ~r1_tarski(A_27, B_28))), inference(demodulation, [status(thm), theory('equality')], [c_29, c_57])).
% 1.62/1.15  tff(c_90, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(resolution, [status(thm)], [c_16, c_69])).
% 1.62/1.15  tff(c_10, plain, (![A_7, B_8]: (k3_xboole_0(A_7, k2_xboole_0(A_7, B_8))=A_7)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.62/1.15  tff(c_94, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_90, c_10])).
% 1.62/1.15  tff(c_101, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_94])).
% 1.62/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.15  
% 1.62/1.15  Inference rules
% 1.62/1.15  ----------------------
% 1.62/1.15  #Ref     : 0
% 1.62/1.15  #Sup     : 19
% 1.62/1.15  #Fact    : 0
% 1.62/1.15  #Define  : 0
% 1.62/1.15  #Split   : 0
% 1.62/1.15  #Chain   : 0
% 1.62/1.15  #Close   : 0
% 1.62/1.15  
% 1.62/1.15  Ordering : KBO
% 1.62/1.15  
% 1.62/1.15  Simplification rules
% 1.62/1.15  ----------------------
% 1.62/1.15  #Subsume      : 0
% 1.62/1.15  #Demod        : 3
% 1.62/1.15  #Tautology    : 8
% 1.62/1.15  #SimpNegUnit  : 1
% 1.62/1.15  #BackRed      : 0
% 1.62/1.15  
% 1.62/1.15  #Partial instantiations: 0
% 1.62/1.15  #Strategies tried      : 1
% 1.62/1.15  
% 1.62/1.15  Timing (in seconds)
% 1.62/1.15  ----------------------
% 1.62/1.16  Preprocessing        : 0.27
% 1.62/1.16  Parsing              : 0.15
% 1.62/1.16  CNF conversion       : 0.02
% 1.62/1.16  Main loop            : 0.11
% 1.62/1.16  Inferencing          : 0.05
% 1.62/1.16  Reduction            : 0.03
% 1.62/1.16  Demodulation         : 0.02
% 1.62/1.16  BG Simplification    : 0.01
% 1.62/1.16  Subsumption          : 0.02
% 1.62/1.16  Abstraction          : 0.01
% 1.62/1.16  MUC search           : 0.00
% 1.62/1.16  Cooper               : 0.00
% 1.62/1.16  Total                : 0.40
% 1.62/1.16  Index Insertion      : 0.00
% 1.62/1.16  Index Deletion       : 0.00
% 1.62/1.16  Index Matching       : 0.00
% 1.62/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

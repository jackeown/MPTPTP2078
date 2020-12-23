%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:35 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   25 (  27 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  36 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_45,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_25,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_8,plain,(
    ! [A_2,B_3,C_4] :
      ( r1_tarski('#skF_1'(A_2,B_3,C_4),B_3)
      | k3_xboole_0(B_3,C_4) = A_2
      | ~ r1_tarski(A_2,C_4)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_29,plain,(
    ! [A_18,B_19,C_20] :
      ( ~ r1_tarski('#skF_1'(A_18,B_19,C_20),A_18)
      | k3_xboole_0(B_19,C_20) = A_18
      | ~ r1_tarski(A_18,C_20)
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_33,plain,(
    ! [B_3,C_4] :
      ( k3_xboole_0(B_3,C_4) = B_3
      | ~ r1_tarski(B_3,C_4)
      | ~ r1_tarski(B_3,B_3) ) ),
    inference(resolution,[status(thm)],[c_8,c_29])).

tff(c_44,plain,(
    ! [B_21,C_22] :
      ( k3_xboole_0(B_21,C_22) = B_21
      | ~ r1_tarski(B_21,C_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_25,c_33])).

tff(c_60,plain,(
    ! [A_6,B_7] : k3_xboole_0(A_6,k2_xboole_0(A_6,B_7)) = A_6 ),
    inference(resolution,[status(thm)],[c_10,c_44])).

tff(c_12,plain,(
    k3_xboole_0('#skF_2',k2_xboole_0('#skF_2','#skF_3')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_72,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_60,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n001.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:38:30 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.18  
% 1.79/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.19  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 1.79/1.19  
% 1.79/1.19  %Foreground sorts:
% 1.79/1.19  
% 1.79/1.19  
% 1.79/1.19  %Background operators:
% 1.79/1.19  
% 1.79/1.19  
% 1.79/1.19  %Foreground operators:
% 1.79/1.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.79/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.19  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.19  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.79/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.79/1.19  
% 1.79/1.19  tff(f_42, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.79/1.19  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.79/1.19  tff(f_40, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 1.79/1.19  tff(f_45, negated_conjecture, ~(![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.79/1.19  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.79/1.19  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.79/1.19  tff(c_22, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.79/1.19  tff(c_25, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_22])).
% 1.79/1.19  tff(c_8, plain, (![A_2, B_3, C_4]: (r1_tarski('#skF_1'(A_2, B_3, C_4), B_3) | k3_xboole_0(B_3, C_4)=A_2 | ~r1_tarski(A_2, C_4) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.79/1.19  tff(c_29, plain, (![A_18, B_19, C_20]: (~r1_tarski('#skF_1'(A_18, B_19, C_20), A_18) | k3_xboole_0(B_19, C_20)=A_18 | ~r1_tarski(A_18, C_20) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.79/1.19  tff(c_33, plain, (![B_3, C_4]: (k3_xboole_0(B_3, C_4)=B_3 | ~r1_tarski(B_3, C_4) | ~r1_tarski(B_3, B_3))), inference(resolution, [status(thm)], [c_8, c_29])).
% 1.79/1.19  tff(c_44, plain, (![B_21, C_22]: (k3_xboole_0(B_21, C_22)=B_21 | ~r1_tarski(B_21, C_22))), inference(demodulation, [status(thm), theory('equality')], [c_25, c_33])).
% 1.79/1.19  tff(c_60, plain, (![A_6, B_7]: (k3_xboole_0(A_6, k2_xboole_0(A_6, B_7))=A_6)), inference(resolution, [status(thm)], [c_10, c_44])).
% 1.79/1.19  tff(c_12, plain, (k3_xboole_0('#skF_2', k2_xboole_0('#skF_2', '#skF_3'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.79/1.19  tff(c_72, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_60, c_12])).
% 1.79/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.19  
% 1.79/1.19  Inference rules
% 1.79/1.19  ----------------------
% 1.79/1.19  #Ref     : 0
% 1.79/1.19  #Sup     : 11
% 1.79/1.19  #Fact    : 0
% 1.79/1.19  #Define  : 0
% 1.79/1.19  #Split   : 0
% 1.79/1.19  #Chain   : 0
% 1.79/1.19  #Close   : 0
% 1.79/1.19  
% 1.79/1.19  Ordering : KBO
% 1.79/1.19  
% 1.79/1.19  Simplification rules
% 1.79/1.19  ----------------------
% 1.79/1.19  #Subsume      : 0
% 1.79/1.19  #Demod        : 3
% 1.79/1.19  #Tautology    : 4
% 1.79/1.19  #SimpNegUnit  : 0
% 1.79/1.19  #BackRed      : 1
% 1.79/1.19  
% 1.79/1.19  #Partial instantiations: 0
% 1.79/1.19  #Strategies tried      : 1
% 1.79/1.19  
% 1.79/1.19  Timing (in seconds)
% 1.79/1.19  ----------------------
% 1.79/1.20  Preprocessing        : 0.28
% 1.79/1.20  Parsing              : 0.15
% 1.79/1.20  CNF conversion       : 0.02
% 1.79/1.20  Main loop            : 0.11
% 1.79/1.20  Inferencing          : 0.05
% 1.79/1.20  Reduction            : 0.03
% 1.79/1.20  Demodulation         : 0.02
% 1.79/1.20  BG Simplification    : 0.01
% 1.79/1.20  Subsumption          : 0.02
% 1.79/1.20  Abstraction          : 0.01
% 1.79/1.20  MUC search           : 0.00
% 1.79/1.20  Cooper               : 0.00
% 1.79/1.20  Total                : 0.41
% 1.79/1.20  Index Insertion      : 0.00
% 1.79/1.20  Index Deletion       : 0.00
% 1.79/1.20  Index Matching       : 0.00
% 1.79/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:40 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   25 (  27 expanded)
%              Number of leaves         :   14 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  38 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

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

tff(f_47,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,B)
       => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_42,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

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

tff(c_12,plain,(
    k3_xboole_0('#skF_2','#skF_3') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_9,B_10] : r1_tarski(A_9,k2_xboole_0(A_9,B_10)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_27,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_24])).

tff(c_8,plain,(
    ! [A_2,B_3,C_4] :
      ( r1_tarski('#skF_1'(A_2,B_3,C_4),B_3)
      | k3_xboole_0(B_3,C_4) = A_2
      | ~ r1_tarski(A_2,C_4)
      | ~ r1_tarski(A_2,B_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_31,plain,(
    ! [A_18,B_19,C_20] :
      ( ~ r1_tarski('#skF_1'(A_18,B_19,C_20),A_18)
      | k3_xboole_0(B_19,C_20) = A_18
      | ~ r1_tarski(A_18,C_20)
      | ~ r1_tarski(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_35,plain,(
    ! [B_3,C_4] :
      ( k3_xboole_0(B_3,C_4) = B_3
      | ~ r1_tarski(B_3,C_4)
      | ~ r1_tarski(B_3,B_3) ) ),
    inference(resolution,[status(thm)],[c_8,c_31])).

tff(c_46,plain,(
    ! [B_21,C_22] :
      ( k3_xboole_0(B_21,C_22) = B_21
      | ~ r1_tarski(B_21,C_22) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_27,c_35])).

tff(c_61,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_14,c_46])).

tff(c_69,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n018.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:12:42 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.17  
% 1.62/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.17  %$ r1_tarski > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_1 > #skF_2 > #skF_3
% 1.62/1.17  
% 1.62/1.17  %Foreground sorts:
% 1.62/1.17  
% 1.62/1.17  
% 1.62/1.17  %Background operators:
% 1.62/1.17  
% 1.62/1.17  
% 1.62/1.17  %Foreground operators:
% 1.62/1.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.62/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.62/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.62/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.62/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.62/1.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.62/1.17  
% 1.62/1.18  tff(f_47, negated_conjecture, ~(![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.62/1.18  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.62/1.18  tff(f_42, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.62/1.18  tff(f_40, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_xboole_1)).
% 1.62/1.18  tff(c_12, plain, (k3_xboole_0('#skF_2', '#skF_3')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.62/1.18  tff(c_14, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.62/1.18  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.62/1.18  tff(c_24, plain, (![A_9, B_10]: (r1_tarski(A_9, k2_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.62/1.18  tff(c_27, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_24])).
% 1.62/1.18  tff(c_8, plain, (![A_2, B_3, C_4]: (r1_tarski('#skF_1'(A_2, B_3, C_4), B_3) | k3_xboole_0(B_3, C_4)=A_2 | ~r1_tarski(A_2, C_4) | ~r1_tarski(A_2, B_3))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.62/1.18  tff(c_31, plain, (![A_18, B_19, C_20]: (~r1_tarski('#skF_1'(A_18, B_19, C_20), A_18) | k3_xboole_0(B_19, C_20)=A_18 | ~r1_tarski(A_18, C_20) | ~r1_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.62/1.18  tff(c_35, plain, (![B_3, C_4]: (k3_xboole_0(B_3, C_4)=B_3 | ~r1_tarski(B_3, C_4) | ~r1_tarski(B_3, B_3))), inference(resolution, [status(thm)], [c_8, c_31])).
% 1.62/1.18  tff(c_46, plain, (![B_21, C_22]: (k3_xboole_0(B_21, C_22)=B_21 | ~r1_tarski(B_21, C_22))), inference(demodulation, [status(thm), theory('equality')], [c_27, c_35])).
% 1.62/1.18  tff(c_61, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_14, c_46])).
% 1.62/1.18  tff(c_69, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_61])).
% 1.62/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.18  
% 1.62/1.18  Inference rules
% 1.62/1.18  ----------------------
% 1.62/1.18  #Ref     : 0
% 1.62/1.18  #Sup     : 10
% 1.62/1.18  #Fact    : 0
% 1.62/1.18  #Define  : 0
% 1.62/1.18  #Split   : 0
% 1.62/1.18  #Chain   : 0
% 1.62/1.18  #Close   : 0
% 1.62/1.18  
% 1.62/1.18  Ordering : KBO
% 1.62/1.18  
% 1.62/1.18  Simplification rules
% 1.62/1.18  ----------------------
% 1.62/1.18  #Subsume      : 0
% 1.62/1.18  #Demod        : 2
% 1.62/1.18  #Tautology    : 2
% 1.62/1.18  #SimpNegUnit  : 1
% 1.62/1.18  #BackRed      : 0
% 1.62/1.18  
% 1.62/1.18  #Partial instantiations: 0
% 1.62/1.18  #Strategies tried      : 1
% 1.62/1.18  
% 1.62/1.18  Timing (in seconds)
% 1.62/1.18  ----------------------
% 1.62/1.18  Preprocessing        : 0.27
% 1.62/1.18  Parsing              : 0.15
% 1.62/1.18  CNF conversion       : 0.02
% 1.62/1.18  Main loop            : 0.11
% 1.62/1.18  Inferencing          : 0.05
% 1.62/1.18  Reduction            : 0.03
% 1.62/1.18  Demodulation         : 0.02
% 1.62/1.18  BG Simplification    : 0.01
% 1.62/1.18  Subsumption          : 0.02
% 1.62/1.18  Abstraction          : 0.01
% 1.62/1.18  MUC search           : 0.00
% 1.62/1.18  Cooper               : 0.00
% 1.62/1.18  Total                : 0.40
% 1.62/1.18  Index Insertion      : 0.00
% 1.62/1.18  Index Deletion       : 0.00
% 1.79/1.18  Index Matching       : 0.00
% 1.79/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

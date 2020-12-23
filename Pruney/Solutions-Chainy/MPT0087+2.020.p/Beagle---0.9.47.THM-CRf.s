%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:19 EST 2020

% Result     : Theorem 1.78s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   23 (  24 expanded)
%              Number of leaves         :   14 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  25 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_14,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_16,plain,(
    ! [A_10,B_11] :
      ( k2_xboole_0(A_10,B_11) = B_11
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_20,plain,(
    ! [A_3,B_4] : k2_xboole_0(k4_xboole_0(A_3,B_4),A_3) = A_3 ),
    inference(resolution,[status(thm)],[c_4,c_16])).

tff(c_34,plain,(
    ! [A_17,B_18,C_19] :
      ( r1_xboole_0(A_17,B_18)
      | ~ r1_xboole_0(A_17,k2_xboole_0(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_38,plain,(
    ! [A_20,A_21,B_22] :
      ( r1_xboole_0(A_20,k4_xboole_0(A_21,B_22))
      | ~ r1_xboole_0(A_20,A_21) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_34])).

tff(c_12,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_41,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_38,c_12])).

tff(c_45,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_41])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:38:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.78/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.26  
% 1.78/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.26  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.78/1.26  
% 1.78/1.26  %Foreground sorts:
% 1.78/1.26  
% 1.78/1.26  
% 1.78/1.26  %Background operators:
% 1.78/1.26  
% 1.78/1.26  
% 1.78/1.26  %Foreground operators:
% 1.78/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.78/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.78/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.78/1.26  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.78/1.26  tff('#skF_2', type, '#skF_2': $i).
% 1.78/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.78/1.26  tff('#skF_1', type, '#skF_1': $i).
% 1.78/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.78/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.78/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.78/1.26  
% 1.78/1.27  tff(f_52, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t80_xboole_1)).
% 1.78/1.27  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.78/1.27  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.78/1.27  tff(f_47, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 1.78/1.27  tff(c_14, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.78/1.27  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.78/1.27  tff(c_16, plain, (![A_10, B_11]: (k2_xboole_0(A_10, B_11)=B_11 | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.78/1.27  tff(c_20, plain, (![A_3, B_4]: (k2_xboole_0(k4_xboole_0(A_3, B_4), A_3)=A_3)), inference(resolution, [status(thm)], [c_4, c_16])).
% 1.78/1.27  tff(c_34, plain, (![A_17, B_18, C_19]: (r1_xboole_0(A_17, B_18) | ~r1_xboole_0(A_17, k2_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.78/1.27  tff(c_38, plain, (![A_20, A_21, B_22]: (r1_xboole_0(A_20, k4_xboole_0(A_21, B_22)) | ~r1_xboole_0(A_20, A_21))), inference(superposition, [status(thm), theory('equality')], [c_20, c_34])).
% 1.78/1.27  tff(c_12, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.78/1.27  tff(c_41, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_38, c_12])).
% 1.78/1.27  tff(c_45, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_41])).
% 1.78/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.78/1.27  
% 1.78/1.27  Inference rules
% 1.78/1.27  ----------------------
% 1.78/1.27  #Ref     : 0
% 1.78/1.27  #Sup     : 6
% 1.78/1.27  #Fact    : 0
% 1.78/1.27  #Define  : 0
% 1.78/1.27  #Split   : 0
% 1.78/1.27  #Chain   : 0
% 1.78/1.27  #Close   : 0
% 1.78/1.27  
% 1.78/1.27  Ordering : KBO
% 1.78/1.27  
% 1.78/1.27  Simplification rules
% 1.78/1.27  ----------------------
% 1.78/1.27  #Subsume      : 0
% 1.78/1.27  #Demod        : 1
% 1.78/1.27  #Tautology    : 3
% 1.78/1.27  #SimpNegUnit  : 0
% 1.78/1.27  #BackRed      : 0
% 1.78/1.27  
% 1.78/1.27  #Partial instantiations: 0
% 1.78/1.27  #Strategies tried      : 1
% 1.78/1.27  
% 1.78/1.27  Timing (in seconds)
% 1.78/1.27  ----------------------
% 1.78/1.27  Preprocessing        : 0.36
% 1.78/1.27  Parsing              : 0.17
% 1.78/1.27  CNF conversion       : 0.03
% 1.78/1.27  Main loop            : 0.10
% 1.78/1.27  Inferencing          : 0.05
% 1.78/1.27  Reduction            : 0.02
% 1.78/1.27  Demodulation         : 0.02
% 1.78/1.28  BG Simplification    : 0.02
% 1.78/1.28  Subsumption          : 0.01
% 1.78/1.28  Abstraction          : 0.00
% 1.78/1.28  MUC search           : 0.00
% 1.78/1.28  Cooper               : 0.00
% 1.78/1.28  Total                : 0.48
% 1.78/1.28  Index Insertion      : 0.00
% 1.78/1.28  Index Deletion       : 0.00
% 1.78/1.28  Index Matching       : 0.00
% 1.78/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------

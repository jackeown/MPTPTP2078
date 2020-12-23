%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:59 EST 2020

% Result     : Theorem 1.57s
% Output     : CNFRefutation 1.57s
% Verified   : 
% Statistics : Number of formulae       :   24 (  25 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    5
%              Number of atoms          :   23 (  25 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
          & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_16,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_20,plain,(
    ! [A_14,B_15] :
      ( k2_xboole_0(A_14,B_15) = B_15
      | ~ r1_tarski(A_14,B_15) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_3,B_4] : k2_xboole_0(k3_xboole_0(A_3,B_4),A_3) = A_3 ),
    inference(resolution,[status(thm)],[c_4,c_20])).

tff(c_34,plain,(
    ! [A_18,B_19,C_20] :
      ( r1_xboole_0(A_18,B_19)
      | ~ r1_xboole_0(A_18,k2_xboole_0(B_19,C_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_111,plain,(
    ! [A_33,A_34,B_35] :
      ( r1_xboole_0(A_33,k3_xboole_0(A_34,B_35))
      | ~ r1_xboole_0(A_33,A_34) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_34])).

tff(c_18,plain,(
    ~ r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_114,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_111,c_18])).

tff(c_121,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_114])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.14  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.15  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.36  % Computer   : n008.cluster.edu
% 0.14/0.36  % Model      : x86_64 x86_64
% 0.14/0.36  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.36  % Memory     : 8042.1875MB
% 0.14/0.36  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.36  % CPULimit   : 60
% 0.14/0.36  % DateTime   : Tue Dec  1 10:54:15 EST 2020
% 0.14/0.36  % CPUTime    : 
% 0.14/0.37  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.57/1.13  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.14  
% 1.57/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.14  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.57/1.14  
% 1.57/1.14  %Foreground sorts:
% 1.57/1.14  
% 1.57/1.14  
% 1.57/1.14  %Background operators:
% 1.57/1.14  
% 1.57/1.14  
% 1.57/1.14  %Foreground operators:
% 1.57/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.57/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.57/1.14  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.57/1.14  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.57/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.57/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.57/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.57/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.57/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.57/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.57/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.57/1.14  
% 1.57/1.15  tff(f_58, negated_conjecture, ~(![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 1.57/1.15  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.57/1.15  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.57/1.15  tff(f_51, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 1.57/1.15  tff(c_16, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.57/1.15  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.57/1.15  tff(c_20, plain, (![A_14, B_15]: (k2_xboole_0(A_14, B_15)=B_15 | ~r1_tarski(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.57/1.15  tff(c_24, plain, (![A_3, B_4]: (k2_xboole_0(k3_xboole_0(A_3, B_4), A_3)=A_3)), inference(resolution, [status(thm)], [c_4, c_20])).
% 1.57/1.15  tff(c_34, plain, (![A_18, B_19, C_20]: (r1_xboole_0(A_18, B_19) | ~r1_xboole_0(A_18, k2_xboole_0(B_19, C_20)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.57/1.15  tff(c_111, plain, (![A_33, A_34, B_35]: (r1_xboole_0(A_33, k3_xboole_0(A_34, B_35)) | ~r1_xboole_0(A_33, A_34))), inference(superposition, [status(thm), theory('equality')], [c_24, c_34])).
% 1.57/1.15  tff(c_18, plain, (~r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.57/1.15  tff(c_114, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_111, c_18])).
% 1.57/1.15  tff(c_121, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_16, c_114])).
% 1.57/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.57/1.15  
% 1.57/1.15  Inference rules
% 1.57/1.15  ----------------------
% 1.57/1.15  #Ref     : 0
% 1.57/1.15  #Sup     : 24
% 1.57/1.15  #Fact    : 0
% 1.57/1.15  #Define  : 0
% 1.57/1.15  #Split   : 0
% 1.57/1.15  #Chain   : 0
% 1.57/1.15  #Close   : 0
% 1.57/1.15  
% 1.57/1.15  Ordering : KBO
% 1.57/1.15  
% 1.57/1.15  Simplification rules
% 1.57/1.15  ----------------------
% 1.57/1.15  #Subsume      : 0
% 1.57/1.15  #Demod        : 10
% 1.57/1.15  #Tautology    : 17
% 1.57/1.15  #SimpNegUnit  : 0
% 1.57/1.15  #BackRed      : 0
% 1.57/1.15  
% 1.57/1.15  #Partial instantiations: 0
% 1.57/1.15  #Strategies tried      : 1
% 1.57/1.15  
% 1.57/1.15  Timing (in seconds)
% 1.57/1.15  ----------------------
% 1.57/1.15  Preprocessing        : 0.26
% 1.57/1.15  Parsing              : 0.15
% 1.57/1.15  CNF conversion       : 0.02
% 1.57/1.15  Main loop            : 0.12
% 1.57/1.15  Inferencing          : 0.05
% 1.57/1.15  Reduction            : 0.03
% 1.57/1.15  Demodulation         : 0.02
% 1.57/1.15  BG Simplification    : 0.01
% 1.57/1.15  Subsumption          : 0.02
% 1.57/1.15  Abstraction          : 0.01
% 1.57/1.15  MUC search           : 0.00
% 1.57/1.15  Cooper               : 0.00
% 1.57/1.15  Total                : 0.40
% 1.57/1.15  Index Insertion      : 0.00
% 1.57/1.15  Index Deletion       : 0.00
% 1.57/1.15  Index Matching       : 0.00
% 1.57/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 09:44:03 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.24s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  38 expanded)
%              Number of equality atoms :    4 (   6 expanded)
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

tff(f_29,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t63_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_22,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_267,plain,(
    ! [A_43,C_44,B_45] :
      ( r1_xboole_0(A_43,C_44)
      | ~ r1_xboole_0(B_45,C_44)
      | ~ r1_tarski(A_43,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_270,plain,(
    ! [A_43] :
      ( r1_xboole_0(A_43,'#skF_2')
      | ~ r1_tarski(A_43,'#skF_1') ) ),
    inference(resolution,[status(thm)],[c_22,c_267])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_91,plain,(
    ! [A_31,B_32] : k2_xboole_0(k3_xboole_0(A_31,B_32),k4_xboole_0(A_31,B_32)) = A_31 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_18,plain,(
    ! [A_14,B_15,C_16] :
      ( r1_xboole_0(A_14,B_15)
      | ~ r1_xboole_0(A_14,k2_xboole_0(B_15,C_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_471,plain,(
    ! [A_62,A_63,B_64] :
      ( r1_xboole_0(A_62,k3_xboole_0(A_63,B_64))
      | ~ r1_xboole_0(A_62,A_63) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_18])).

tff(c_550,plain,(
    ! [A_70,B_71,A_72] :
      ( r1_xboole_0(A_70,k3_xboole_0(B_71,A_72))
      | ~ r1_xboole_0(A_70,A_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_471])).

tff(c_20,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_23,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_20])).

tff(c_569,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_550,c_23])).

tff(c_572,plain,(
    ~ r1_tarski(k3_xboole_0('#skF_1','#skF_3'),'#skF_1') ),
    inference(resolution,[status(thm)],[c_270,c_569])).

tff(c_576,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_572])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:33:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.36  
% 2.24/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.36  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 2.24/1.36  
% 2.24/1.36  %Foreground sorts:
% 2.24/1.36  
% 2.24/1.36  
% 2.24/1.36  %Background operators:
% 2.24/1.36  
% 2.24/1.36  
% 2.24/1.36  %Foreground operators:
% 2.24/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.24/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.24/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.24/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.24/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.24/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.24/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.24/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.24/1.36  
% 2.24/1.37  tff(f_29, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.24/1.37  tff(f_62, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_xboole_1)).
% 2.24/1.37  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t63_xboole_1)).
% 2.24/1.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.24/1.37  tff(f_35, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t51_xboole_1)).
% 2.24/1.37  tff(f_57, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 2.24/1.37  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.24/1.37  tff(c_22, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.24/1.37  tff(c_267, plain, (![A_43, C_44, B_45]: (r1_xboole_0(A_43, C_44) | ~r1_xboole_0(B_45, C_44) | ~r1_tarski(A_43, B_45))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.24/1.37  tff(c_270, plain, (![A_43]: (r1_xboole_0(A_43, '#skF_2') | ~r1_tarski(A_43, '#skF_1'))), inference(resolution, [status(thm)], [c_22, c_267])).
% 2.24/1.37  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.24/1.37  tff(c_91, plain, (![A_31, B_32]: (k2_xboole_0(k3_xboole_0(A_31, B_32), k4_xboole_0(A_31, B_32))=A_31)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.24/1.37  tff(c_18, plain, (![A_14, B_15, C_16]: (r1_xboole_0(A_14, B_15) | ~r1_xboole_0(A_14, k2_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.24/1.37  tff(c_471, plain, (![A_62, A_63, B_64]: (r1_xboole_0(A_62, k3_xboole_0(A_63, B_64)) | ~r1_xboole_0(A_62, A_63))), inference(superposition, [status(thm), theory('equality')], [c_91, c_18])).
% 2.24/1.37  tff(c_550, plain, (![A_70, B_71, A_72]: (r1_xboole_0(A_70, k3_xboole_0(B_71, A_72)) | ~r1_xboole_0(A_70, A_72))), inference(superposition, [status(thm), theory('equality')], [c_2, c_471])).
% 2.24/1.37  tff(c_20, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.24/1.37  tff(c_23, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_20])).
% 2.24/1.37  tff(c_569, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_550, c_23])).
% 2.24/1.37  tff(c_572, plain, (~r1_tarski(k3_xboole_0('#skF_1', '#skF_3'), '#skF_1')), inference(resolution, [status(thm)], [c_270, c_569])).
% 2.24/1.37  tff(c_576, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_4, c_572])).
% 2.24/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.24/1.37  
% 2.24/1.37  Inference rules
% 2.24/1.37  ----------------------
% 2.24/1.37  #Ref     : 0
% 2.24/1.37  #Sup     : 143
% 2.24/1.37  #Fact    : 0
% 2.24/1.37  #Define  : 0
% 2.24/1.37  #Split   : 0
% 2.24/1.37  #Chain   : 0
% 2.24/1.37  #Close   : 0
% 2.24/1.37  
% 2.24/1.37  Ordering : KBO
% 2.24/1.37  
% 2.24/1.37  Simplification rules
% 2.24/1.37  ----------------------
% 2.24/1.37  #Subsume      : 13
% 2.24/1.37  #Demod        : 85
% 2.24/1.37  #Tautology    : 81
% 2.24/1.37  #SimpNegUnit  : 0
% 2.24/1.37  #BackRed      : 0
% 2.24/1.37  
% 2.24/1.37  #Partial instantiations: 0
% 2.24/1.37  #Strategies tried      : 1
% 2.24/1.37  
% 2.24/1.37  Timing (in seconds)
% 2.24/1.37  ----------------------
% 2.24/1.37  Preprocessing        : 0.27
% 2.24/1.37  Parsing              : 0.15
% 2.24/1.37  CNF conversion       : 0.02
% 2.24/1.37  Main loop            : 0.27
% 2.24/1.37  Inferencing          : 0.09
% 2.24/1.37  Reduction            : 0.11
% 2.24/1.37  Demodulation         : 0.09
% 2.24/1.37  BG Simplification    : 0.01
% 2.24/1.37  Subsumption          : 0.04
% 2.24/1.37  Abstraction          : 0.01
% 2.24/1.37  MUC search           : 0.00
% 2.24/1.37  Cooper               : 0.00
% 2.24/1.37  Total                : 0.57
% 2.24/1.37  Index Insertion      : 0.00
% 2.24/1.37  Index Deletion       : 0.00
% 2.24/1.37  Index Matching       : 0.00
% 2.24/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------

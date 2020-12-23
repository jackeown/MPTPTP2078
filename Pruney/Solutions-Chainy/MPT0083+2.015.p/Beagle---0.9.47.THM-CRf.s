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
% DateTime   : Thu Dec  3 09:44:03 EST 2020

% Result     : Theorem 1.98s
% Output     : CNFRefutation 1.98s
% Verified   : 
% Statistics : Number of formulae       :   30 (  39 expanded)
%              Number of leaves         :   15 (  20 expanded)
%              Depth                    :    6
%              Number of atoms          :   33 (  51 expanded)
%              Number of equality atoms :    4 (   8 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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
        ( r1_xboole_0(A,B)
       => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_20,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_31,plain,(
    ! [B_16,A_17] :
      ( r1_xboole_0(B_16,A_17)
      | ~ r1_xboole_0(A_17,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_34,plain,(
    r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_20,c_31])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_149,plain,(
    ! [A_29,C_30,B_31] :
      ( r1_xboole_0(A_29,C_30)
      | ~ r1_xboole_0(A_29,k2_xboole_0(B_31,C_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_265,plain,(
    ! [A_41,A_42,B_43] :
      ( r1_xboole_0(A_41,k3_xboole_0(A_42,B_43))
      | ~ r1_xboole_0(A_41,A_42) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_149])).

tff(c_4,plain,(
    ! [B_4,A_3] :
      ( r1_xboole_0(B_4,A_3)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_455,plain,(
    ! [A_57,B_58,A_59] :
      ( r1_xboole_0(k3_xboole_0(A_57,B_58),A_59)
      | ~ r1_xboole_0(A_59,A_57) ) ),
    inference(resolution,[status(thm)],[c_265,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_333,plain,(
    ! [A_46,B_47,A_48] :
      ( r1_xboole_0(A_46,k3_xboole_0(B_47,A_48))
      | ~ r1_xboole_0(A_46,A_48) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_265])).

tff(c_18,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_3','#skF_1'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_21,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),k3_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_18])).

tff(c_351,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_3'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_333,c_21])).

tff(c_458,plain,(
    ~ r1_xboole_0('#skF_2','#skF_1') ),
    inference(resolution,[status(thm)],[c_455,c_351])).

tff(c_493,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_458])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n008.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:18:00 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.98/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.31  
% 1.98/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.31  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.98/1.31  
% 1.98/1.31  %Foreground sorts:
% 1.98/1.31  
% 1.98/1.31  
% 1.98/1.31  %Background operators:
% 1.98/1.31  
% 1.98/1.31  
% 1.98/1.31  %Foreground operators:
% 1.98/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.98/1.31  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.98/1.31  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.98/1.31  tff('#skF_2', type, '#skF_2': $i).
% 1.98/1.31  tff('#skF_3', type, '#skF_3': $i).
% 1.98/1.31  tff('#skF_1', type, '#skF_1': $i).
% 1.98/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.98/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.98/1.31  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.98/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.98/1.32  
% 1.98/1.33  tff(f_58, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 1.98/1.33  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.98/1.33  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 1.98/1.33  tff(f_53, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 1.98/1.33  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.98/1.33  tff(c_20, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.98/1.33  tff(c_31, plain, (![B_16, A_17]: (r1_xboole_0(B_16, A_17) | ~r1_xboole_0(A_17, B_16))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.33  tff(c_34, plain, (r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_20, c_31])).
% 1.98/1.33  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.98/1.33  tff(c_149, plain, (![A_29, C_30, B_31]: (r1_xboole_0(A_29, C_30) | ~r1_xboole_0(A_29, k2_xboole_0(B_31, C_30)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.98/1.33  tff(c_265, plain, (![A_41, A_42, B_43]: (r1_xboole_0(A_41, k3_xboole_0(A_42, B_43)) | ~r1_xboole_0(A_41, A_42))), inference(superposition, [status(thm), theory('equality')], [c_6, c_149])).
% 1.98/1.33  tff(c_4, plain, (![B_4, A_3]: (r1_xboole_0(B_4, A_3) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.98/1.33  tff(c_455, plain, (![A_57, B_58, A_59]: (r1_xboole_0(k3_xboole_0(A_57, B_58), A_59) | ~r1_xboole_0(A_59, A_57))), inference(resolution, [status(thm)], [c_265, c_4])).
% 1.98/1.33  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.98/1.33  tff(c_333, plain, (![A_46, B_47, A_48]: (r1_xboole_0(A_46, k3_xboole_0(B_47, A_48)) | ~r1_xboole_0(A_46, A_48))), inference(superposition, [status(thm), theory('equality')], [c_2, c_265])).
% 1.98/1.33  tff(c_18, plain, (~r1_xboole_0(k3_xboole_0('#skF_3', '#skF_1'), k3_xboole_0('#skF_3', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.98/1.33  tff(c_21, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), k3_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_18])).
% 1.98/1.33  tff(c_351, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_3'), '#skF_2')), inference(resolution, [status(thm)], [c_333, c_21])).
% 1.98/1.33  tff(c_458, plain, (~r1_xboole_0('#skF_2', '#skF_1')), inference(resolution, [status(thm)], [c_455, c_351])).
% 1.98/1.33  tff(c_493, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_458])).
% 1.98/1.33  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.98/1.33  
% 1.98/1.33  Inference rules
% 1.98/1.33  ----------------------
% 1.98/1.33  #Ref     : 0
% 1.98/1.33  #Sup     : 123
% 1.98/1.33  #Fact    : 0
% 1.98/1.33  #Define  : 0
% 1.98/1.33  #Split   : 0
% 1.98/1.33  #Chain   : 0
% 1.98/1.33  #Close   : 0
% 1.98/1.33  
% 1.98/1.33  Ordering : KBO
% 1.98/1.33  
% 1.98/1.33  Simplification rules
% 1.98/1.33  ----------------------
% 1.98/1.33  #Subsume      : 13
% 1.98/1.33  #Demod        : 50
% 1.98/1.33  #Tautology    : 66
% 1.98/1.33  #SimpNegUnit  : 0
% 1.98/1.33  #BackRed      : 0
% 1.98/1.33  
% 1.98/1.33  #Partial instantiations: 0
% 1.98/1.33  #Strategies tried      : 1
% 1.98/1.33  
% 1.98/1.33  Timing (in seconds)
% 1.98/1.33  ----------------------
% 1.98/1.33  Preprocessing        : 0.28
% 1.98/1.33  Parsing              : 0.16
% 1.98/1.33  CNF conversion       : 0.02
% 1.98/1.33  Main loop            : 0.27
% 1.98/1.33  Inferencing          : 0.09
% 1.98/1.33  Reduction            : 0.10
% 1.98/1.33  Demodulation         : 0.08
% 1.98/1.33  BG Simplification    : 0.01
% 1.98/1.33  Subsumption          : 0.04
% 1.98/1.33  Abstraction          : 0.01
% 1.98/1.33  MUC search           : 0.00
% 1.98/1.33  Cooper               : 0.00
% 1.98/1.33  Total                : 0.57
% 1.98/1.33  Index Insertion      : 0.00
% 1.98/1.33  Index Deletion       : 0.00
% 1.98/1.33  Index Matching       : 0.00
% 2.33/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------

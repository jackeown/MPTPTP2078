%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:28 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.59s
% Verified   : 
% Statistics : Number of formulae       :   23 (  26 expanded)
%              Number of leaves         :   12 (  15 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  39 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,B)
          & r1_xboole_0(A,C)
          & r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t84_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_14,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_10,plain,(
    r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k4_xboole_0(B_2,A_1)) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_33,plain,(
    ! [A_17,C_18,B_19] :
      ( ~ r1_xboole_0(A_17,C_18)
      | ~ r1_xboole_0(A_17,B_19)
      | r1_xboole_0(A_17,k2_xboole_0(B_19,C_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_45,plain,(
    ! [A_20,B_21,A_22] :
      ( ~ r1_xboole_0(A_20,k4_xboole_0(B_21,A_22))
      | ~ r1_xboole_0(A_20,A_22)
      | r1_xboole_0(A_20,k2_xboole_0(A_22,B_21)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_33])).

tff(c_51,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(resolution,[status(thm)],[c_10,c_45])).

tff(c_55,plain,(
    r1_xboole_0('#skF_1',k2_xboole_0('#skF_3','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_51])).

tff(c_6,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_xboole_0(A_3,k2_xboole_0(B_4,C_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_61,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_55,c_6])).

tff(c_67,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n002.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 18:20:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.10  
% 1.59/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.10  %$ r1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.59/1.10  
% 1.59/1.10  %Foreground sorts:
% 1.59/1.10  
% 1.59/1.10  
% 1.59/1.10  %Background operators:
% 1.59/1.10  
% 1.59/1.10  
% 1.59/1.10  %Foreground operators:
% 1.59/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.10  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.59/1.10  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.59/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.59/1.10  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.59/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.10  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.59/1.10  
% 1.59/1.11  tff(f_52, negated_conjecture, ~(![A, B, C]: ~((~r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t84_xboole_1)).
% 1.59/1.11  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.59/1.11  tff(f_43, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 1.59/1.11  tff(c_14, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.59/1.11  tff(c_12, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.59/1.11  tff(c_10, plain, (r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.59/1.11  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k4_xboole_0(B_2, A_1))=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.59/1.11  tff(c_33, plain, (![A_17, C_18, B_19]: (~r1_xboole_0(A_17, C_18) | ~r1_xboole_0(A_17, B_19) | r1_xboole_0(A_17, k2_xboole_0(B_19, C_18)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.59/1.11  tff(c_45, plain, (![A_20, B_21, A_22]: (~r1_xboole_0(A_20, k4_xboole_0(B_21, A_22)) | ~r1_xboole_0(A_20, A_22) | r1_xboole_0(A_20, k2_xboole_0(A_22, B_21)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_33])).
% 1.59/1.11  tff(c_51, plain, (~r1_xboole_0('#skF_1', '#skF_3') | r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(resolution, [status(thm)], [c_10, c_45])).
% 1.59/1.11  tff(c_55, plain, (r1_xboole_0('#skF_1', k2_xboole_0('#skF_3', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_12, c_51])).
% 1.59/1.11  tff(c_6, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_xboole_0(A_3, k2_xboole_0(B_4, C_5)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.59/1.11  tff(c_61, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_55, c_6])).
% 1.59/1.11  tff(c_67, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_61])).
% 1.59/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.11  
% 1.59/1.11  Inference rules
% 1.59/1.11  ----------------------
% 1.59/1.11  #Ref     : 0
% 1.59/1.11  #Sup     : 11
% 1.59/1.11  #Fact    : 0
% 1.59/1.11  #Define  : 0
% 1.59/1.11  #Split   : 0
% 1.59/1.11  #Chain   : 0
% 1.59/1.11  #Close   : 0
% 1.59/1.11  
% 1.59/1.11  Ordering : KBO
% 1.59/1.11  
% 1.59/1.11  Simplification rules
% 1.59/1.11  ----------------------
% 1.59/1.11  #Subsume      : 1
% 1.59/1.11  #Demod        : 2
% 1.59/1.11  #Tautology    : 6
% 1.59/1.11  #SimpNegUnit  : 1
% 1.59/1.11  #BackRed      : 0
% 1.59/1.11  
% 1.59/1.11  #Partial instantiations: 0
% 1.59/1.11  #Strategies tried      : 1
% 1.59/1.11  
% 1.59/1.11  Timing (in seconds)
% 1.59/1.11  ----------------------
% 1.59/1.11  Preprocessing        : 0.24
% 1.59/1.11  Parsing              : 0.13
% 1.59/1.11  CNF conversion       : 0.02
% 1.59/1.11  Main loop            : 0.10
% 1.59/1.11  Inferencing          : 0.05
% 1.59/1.11  Reduction            : 0.02
% 1.59/1.11  Demodulation         : 0.02
% 1.59/1.11  BG Simplification    : 0.01
% 1.59/1.11  Subsumption          : 0.02
% 1.59/1.11  Abstraction          : 0.00
% 1.59/1.11  MUC search           : 0.00
% 1.59/1.11  Cooper               : 0.00
% 1.59/1.12  Total                : 0.36
% 1.59/1.12  Index Insertion      : 0.00
% 1.59/1.12  Index Deletion       : 0.00
% 1.59/1.12  Index Matching       : 0.00
% 1.59/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------

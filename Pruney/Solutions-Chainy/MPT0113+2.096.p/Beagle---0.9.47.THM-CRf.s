%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:24 EST 2020

% Result     : Theorem 1.91s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   34 (  39 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   40 (  52 expanded)
%              Number of equality atoms :    3 (   3 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,k4_xboole_0(B,C))
       => ( r1_tarski(A,B)
          & r1_xboole_0(A,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t106_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_xboole_0(A,k4_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t85_xboole_1)).

tff(c_16,plain,
    ( ~ r1_xboole_0('#skF_1','#skF_3')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_21,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_18,plain,(
    r1_tarski('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(k4_xboole_0(A_6,B_7),A_6) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_148,plain,(
    ! [A_40,C_41,B_42] :
      ( r1_tarski(A_40,C_41)
      | ~ r1_tarski(B_42,C_41)
      | ~ r1_tarski(A_40,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_158,plain,(
    ! [A_43,A_44,B_45] :
      ( r1_tarski(A_43,A_44)
      | ~ r1_tarski(A_43,k4_xboole_0(A_44,B_45)) ) ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_175,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_18,c_158])).

tff(c_182,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_21,c_175])).

tff(c_183,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_xboole_0(k4_xboole_0(A_8,B_9),B_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_185,plain,(
    ! [B_46,A_47] :
      ( r1_xboole_0(B_46,A_47)
      | ~ r1_xboole_0(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_188,plain,(
    ! [B_9,A_8] : r1_xboole_0(B_9,k4_xboole_0(A_8,B_9)) ),
    inference(resolution,[status(thm)],[c_8,c_185])).

tff(c_194,plain,(
    ! [A_50,B_51] :
      ( k4_xboole_0(A_50,B_51) = A_50
      | ~ r1_xboole_0(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_201,plain,(
    ! [B_9,A_8] : k4_xboole_0(B_9,k4_xboole_0(A_8,B_9)) = B_9 ),
    inference(resolution,[status(thm)],[c_188,c_194])).

tff(c_242,plain,(
    ! [A_57,C_58,B_59] :
      ( r1_xboole_0(A_57,k4_xboole_0(C_58,B_59))
      | ~ r1_tarski(A_57,B_59) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_402,plain,(
    ! [A_80,B_81,A_82] :
      ( r1_xboole_0(A_80,B_81)
      | ~ r1_tarski(A_80,k4_xboole_0(A_82,B_81)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_201,c_242])).

tff(c_426,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_18,c_402])).

tff(c_435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_183,c_426])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n022.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 18:25:56 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.91/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.20  
% 1.91/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.20  %$ r1_xboole_0 > r1_tarski > k4_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.91/1.20  
% 1.91/1.20  %Foreground sorts:
% 1.91/1.20  
% 1.91/1.20  
% 1.91/1.20  %Background operators:
% 1.91/1.20  
% 1.91/1.20  
% 1.91/1.20  %Foreground operators:
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.91/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.91/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.91/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.91/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.20  
% 1.91/1.21  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, k4_xboole_0(B, C)) => (r1_tarski(A, B) & r1_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t106_xboole_1)).
% 1.91/1.21  tff(f_37, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.91/1.21  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.91/1.21  tff(f_39, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.91/1.21  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.91/1.21  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.91/1.21  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_xboole_0(A, k4_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t85_xboole_1)).
% 1.91/1.21  tff(c_16, plain, (~r1_xboole_0('#skF_1', '#skF_3') | ~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.91/1.21  tff(c_21, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_16])).
% 1.91/1.21  tff(c_18, plain, (r1_tarski('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.91/1.21  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(k4_xboole_0(A_6, B_7), A_6))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.91/1.21  tff(c_148, plain, (![A_40, C_41, B_42]: (r1_tarski(A_40, C_41) | ~r1_tarski(B_42, C_41) | ~r1_tarski(A_40, B_42))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.91/1.21  tff(c_158, plain, (![A_43, A_44, B_45]: (r1_tarski(A_43, A_44) | ~r1_tarski(A_43, k4_xboole_0(A_44, B_45)))), inference(resolution, [status(thm)], [c_6, c_148])).
% 1.91/1.21  tff(c_175, plain, (r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_18, c_158])).
% 1.91/1.21  tff(c_182, plain, $false, inference(negUnitSimplification, [status(thm)], [c_21, c_175])).
% 1.91/1.21  tff(c_183, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_16])).
% 1.91/1.21  tff(c_8, plain, (![A_8, B_9]: (r1_xboole_0(k4_xboole_0(A_8, B_9), B_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.91/1.21  tff(c_185, plain, (![B_46, A_47]: (r1_xboole_0(B_46, A_47) | ~r1_xboole_0(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.91/1.21  tff(c_188, plain, (![B_9, A_8]: (r1_xboole_0(B_9, k4_xboole_0(A_8, B_9)))), inference(resolution, [status(thm)], [c_8, c_185])).
% 1.91/1.21  tff(c_194, plain, (![A_50, B_51]: (k4_xboole_0(A_50, B_51)=A_50 | ~r1_xboole_0(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.91/1.21  tff(c_201, plain, (![B_9, A_8]: (k4_xboole_0(B_9, k4_xboole_0(A_8, B_9))=B_9)), inference(resolution, [status(thm)], [c_188, c_194])).
% 1.91/1.21  tff(c_242, plain, (![A_57, C_58, B_59]: (r1_xboole_0(A_57, k4_xboole_0(C_58, B_59)) | ~r1_tarski(A_57, B_59))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.91/1.21  tff(c_402, plain, (![A_80, B_81, A_82]: (r1_xboole_0(A_80, B_81) | ~r1_tarski(A_80, k4_xboole_0(A_82, B_81)))), inference(superposition, [status(thm), theory('equality')], [c_201, c_242])).
% 1.91/1.21  tff(c_426, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_18, c_402])).
% 1.91/1.21  tff(c_435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_183, c_426])).
% 1.91/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.21  
% 1.91/1.21  Inference rules
% 1.91/1.21  ----------------------
% 1.91/1.21  #Ref     : 0
% 1.91/1.21  #Sup     : 101
% 1.91/1.21  #Fact    : 0
% 1.91/1.21  #Define  : 0
% 1.91/1.21  #Split   : 1
% 1.91/1.21  #Chain   : 0
% 1.91/1.21  #Close   : 0
% 1.91/1.21  
% 1.91/1.21  Ordering : KBO
% 1.91/1.21  
% 1.91/1.21  Simplification rules
% 1.91/1.21  ----------------------
% 1.91/1.21  #Subsume      : 11
% 1.91/1.21  #Demod        : 36
% 1.91/1.21  #Tautology    : 46
% 1.91/1.21  #SimpNegUnit  : 2
% 1.91/1.21  #BackRed      : 0
% 1.91/1.21  
% 1.91/1.21  #Partial instantiations: 0
% 1.91/1.21  #Strategies tried      : 1
% 1.91/1.21  
% 1.91/1.21  Timing (in seconds)
% 1.91/1.21  ----------------------
% 1.91/1.22  Preprocessing        : 0.25
% 1.91/1.22  Parsing              : 0.14
% 1.91/1.22  CNF conversion       : 0.02
% 1.91/1.22  Main loop            : 0.23
% 1.91/1.22  Inferencing          : 0.09
% 1.91/1.22  Reduction            : 0.06
% 1.91/1.22  Demodulation         : 0.05
% 1.91/1.22  BG Simplification    : 0.01
% 1.91/1.22  Subsumption          : 0.04
% 1.91/1.22  Abstraction          : 0.01
% 1.91/1.22  MUC search           : 0.00
% 1.91/1.22  Cooper               : 0.00
% 1.91/1.22  Total                : 0.50
% 1.91/1.22  Index Insertion      : 0.00
% 1.91/1.22  Index Deletion       : 0.00
% 1.91/1.22  Index Matching       : 0.00
% 1.91/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------

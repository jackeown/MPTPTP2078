%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:31 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   25 (  31 expanded)
%              Number of leaves         :   13 (  17 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  42 expanded)
%              Number of equality atoms :    2 (   4 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_10,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_54,plain,(
    ! [A_14,C_15,B_16] :
      ( r1_tarski(k2_xboole_0(A_14,C_15),k2_xboole_0(B_16,C_15))
      | ~ r1_tarski(A_14,B_16) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_68,plain,(
    ! [A_14,A_1,B_2] :
      ( r1_tarski(k2_xboole_0(A_14,A_1),k2_xboole_0(A_1,B_2))
      | ~ r1_tarski(A_14,B_2) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_54])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,C_5)
      | ~ r1_tarski(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_128,plain,(
    ! [A_27,B_28,C_29,A_30] :
      ( r1_tarski(A_27,k2_xboole_0(B_28,C_29))
      | ~ r1_tarski(A_27,k2_xboole_0(A_30,C_29))
      | ~ r1_tarski(A_30,B_28) ) ),
    inference(resolution,[status(thm)],[c_54,c_4])).

tff(c_268,plain,(
    ! [A_49,A_50,B_51,B_52] :
      ( r1_tarski(k2_xboole_0(A_49,A_50),k2_xboole_0(B_51,B_52))
      | ~ r1_tarski(A_50,B_51)
      | ~ r1_tarski(A_49,B_52) ) ),
    inference(resolution,[status(thm)],[c_68,c_128])).

tff(c_8,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_3'),k2_xboole_0('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_13,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_3'),k2_xboole_0('#skF_4','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_8])).

tff(c_281,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_268,c_13])).

tff(c_302,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n023.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:34:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.23  
% 2.06/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.24  %$ r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.06/1.24  
% 2.06/1.24  %Foreground sorts:
% 2.06/1.24  
% 2.06/1.24  
% 2.06/1.24  %Background operators:
% 2.06/1.24  
% 2.06/1.24  
% 2.06/1.24  %Foreground operators:
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.24  tff('#skF_3', type, '#skF_3': $i).
% 2.06/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.24  tff('#skF_4', type, '#skF_4': $i).
% 2.06/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.24  
% 2.06/1.24  tff(f_44, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 2.06/1.24  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.06/1.24  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t9_xboole_1)).
% 2.06/1.24  tff(f_33, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.06/1.24  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.06/1.24  tff(c_10, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.06/1.24  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.06/1.24  tff(c_54, plain, (![A_14, C_15, B_16]: (r1_tarski(k2_xboole_0(A_14, C_15), k2_xboole_0(B_16, C_15)) | ~r1_tarski(A_14, B_16))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.06/1.24  tff(c_68, plain, (![A_14, A_1, B_2]: (r1_tarski(k2_xboole_0(A_14, A_1), k2_xboole_0(A_1, B_2)) | ~r1_tarski(A_14, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_54])).
% 2.06/1.24  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, C_5) | ~r1_tarski(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.24  tff(c_128, plain, (![A_27, B_28, C_29, A_30]: (r1_tarski(A_27, k2_xboole_0(B_28, C_29)) | ~r1_tarski(A_27, k2_xboole_0(A_30, C_29)) | ~r1_tarski(A_30, B_28))), inference(resolution, [status(thm)], [c_54, c_4])).
% 2.06/1.24  tff(c_268, plain, (![A_49, A_50, B_51, B_52]: (r1_tarski(k2_xboole_0(A_49, A_50), k2_xboole_0(B_51, B_52)) | ~r1_tarski(A_50, B_51) | ~r1_tarski(A_49, B_52))), inference(resolution, [status(thm)], [c_68, c_128])).
% 2.06/1.24  tff(c_8, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_3'), k2_xboole_0('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.06/1.24  tff(c_13, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_3'), k2_xboole_0('#skF_4', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_8])).
% 2.06/1.24  tff(c_281, plain, (~r1_tarski('#skF_3', '#skF_4') | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_268, c_13])).
% 2.06/1.24  tff(c_302, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_281])).
% 2.06/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.24  
% 2.06/1.24  Inference rules
% 2.06/1.24  ----------------------
% 2.06/1.24  #Ref     : 0
% 2.06/1.24  #Sup     : 87
% 2.06/1.24  #Fact    : 0
% 2.06/1.24  #Define  : 0
% 2.06/1.24  #Split   : 1
% 2.06/1.24  #Chain   : 0
% 2.06/1.24  #Close   : 0
% 2.06/1.24  
% 2.06/1.24  Ordering : KBO
% 2.06/1.24  
% 2.06/1.24  Simplification rules
% 2.06/1.24  ----------------------
% 2.06/1.24  #Subsume      : 16
% 2.06/1.24  #Demod        : 4
% 2.06/1.24  #Tautology    : 9
% 2.06/1.24  #SimpNegUnit  : 0
% 2.06/1.24  #BackRed      : 0
% 2.06/1.24  
% 2.06/1.24  #Partial instantiations: 0
% 2.06/1.24  #Strategies tried      : 1
% 2.06/1.24  
% 2.06/1.24  Timing (in seconds)
% 2.06/1.24  ----------------------
% 2.06/1.25  Preprocessing        : 0.25
% 2.06/1.25  Parsing              : 0.14
% 2.06/1.25  CNF conversion       : 0.01
% 2.06/1.25  Main loop            : 0.24
% 2.06/1.25  Inferencing          : 0.08
% 2.06/1.25  Reduction            : 0.08
% 2.06/1.25  Demodulation         : 0.07
% 2.06/1.25  BG Simplification    : 0.01
% 2.06/1.25  Subsumption          : 0.05
% 2.06/1.25  Abstraction          : 0.01
% 2.06/1.25  MUC search           : 0.00
% 2.06/1.25  Cooper               : 0.00
% 2.06/1.25  Total                : 0.51
% 2.06/1.25  Index Insertion      : 0.00
% 2.06/1.25  Index Deletion       : 0.00
% 2.06/1.25  Index Matching       : 0.00
% 2.06/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

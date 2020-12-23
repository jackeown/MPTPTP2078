%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:44 EST 2020

% Result     : Theorem 2.32s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   23 (  25 expanded)
%              Number of leaves         :   13 (  15 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  35 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k4_xboole_0(A,D),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(A,C),k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t33_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k4_xboole_0(C,B),k4_xboole_0(C,A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_4,plain,(
    ! [A_4,C_6,B_5] :
      ( r1_tarski(k4_xboole_0(A_4,C_6),k4_xboole_0(B_5,C_6))
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_44,plain,(
    ! [C_20,B_21,A_22] :
      ( r1_tarski(k4_xboole_0(C_20,B_21),k4_xboole_0(C_20,A_22))
      | ~ r1_tarski(A_22,B_21) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(B_2,C_3)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_58,plain,(
    ! [A_27,C_28,A_29,B_30] :
      ( r1_tarski(A_27,k4_xboole_0(C_28,A_29))
      | ~ r1_tarski(A_27,k4_xboole_0(C_28,B_30))
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(resolution,[status(thm)],[c_44,c_2])).

tff(c_192,plain,(
    ! [A_50,C_51,B_52,A_53] :
      ( r1_tarski(k4_xboole_0(A_50,C_51),k4_xboole_0(B_52,A_53))
      | ~ r1_tarski(A_53,C_51)
      | ~ r1_tarski(A_50,B_52) ) ),
    inference(resolution,[status(thm)],[c_4,c_58])).

tff(c_8,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_4'),k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_207,plain,
    ( ~ r1_tarski('#skF_3','#skF_4')
    | ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_192,c_8])).

tff(c_217,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_10,c_207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.32/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.70  
% 2.47/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.70  %$ r1_tarski > k4_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.47/1.70  
% 2.47/1.70  %Foreground sorts:
% 2.47/1.70  
% 2.47/1.70  
% 2.47/1.70  %Background operators:
% 2.47/1.70  
% 2.47/1.70  
% 2.47/1.70  %Foreground operators:
% 2.47/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.70  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.47/1.70  tff('#skF_2', type, '#skF_2': $i).
% 2.47/1.70  tff('#skF_3', type, '#skF_3': $i).
% 2.47/1.70  tff('#skF_1', type, '#skF_1': $i).
% 2.47/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.70  tff('#skF_4', type, '#skF_4': $i).
% 2.47/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.70  
% 2.47/1.71  tff(f_46, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k4_xboole_0(A, D), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_xboole_1)).
% 2.47/1.71  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(A, C), k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t33_xboole_1)).
% 2.47/1.71  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k4_xboole_0(C, B), k4_xboole_0(C, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_xboole_1)).
% 2.47/1.71  tff(f_31, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.47/1.71  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.71  tff(c_10, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.71  tff(c_4, plain, (![A_4, C_6, B_5]: (r1_tarski(k4_xboole_0(A_4, C_6), k4_xboole_0(B_5, C_6)) | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.71  tff(c_44, plain, (![C_20, B_21, A_22]: (r1_tarski(k4_xboole_0(C_20, B_21), k4_xboole_0(C_20, A_22)) | ~r1_tarski(A_22, B_21))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.47/1.71  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(B_2, C_3) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.47/1.71  tff(c_58, plain, (![A_27, C_28, A_29, B_30]: (r1_tarski(A_27, k4_xboole_0(C_28, A_29)) | ~r1_tarski(A_27, k4_xboole_0(C_28, B_30)) | ~r1_tarski(A_29, B_30))), inference(resolution, [status(thm)], [c_44, c_2])).
% 2.47/1.71  tff(c_192, plain, (![A_50, C_51, B_52, A_53]: (r1_tarski(k4_xboole_0(A_50, C_51), k4_xboole_0(B_52, A_53)) | ~r1_tarski(A_53, C_51) | ~r1_tarski(A_50, B_52))), inference(resolution, [status(thm)], [c_4, c_58])).
% 2.47/1.71  tff(c_8, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_4'), k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.47/1.71  tff(c_207, plain, (~r1_tarski('#skF_3', '#skF_4') | ~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_192, c_8])).
% 2.47/1.71  tff(c_217, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_10, c_207])).
% 2.47/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.47/1.71  
% 2.47/1.71  Inference rules
% 2.47/1.71  ----------------------
% 2.47/1.71  #Ref     : 0
% 2.47/1.71  #Sup     : 61
% 2.47/1.71  #Fact    : 0
% 2.47/1.71  #Define  : 0
% 2.47/1.71  #Split   : 1
% 2.47/1.71  #Chain   : 0
% 2.47/1.71  #Close   : 0
% 2.47/1.71  
% 2.47/1.71  Ordering : KBO
% 2.47/1.71  
% 2.47/1.71  Simplification rules
% 2.47/1.71  ----------------------
% 2.47/1.71  #Subsume      : 1
% 2.47/1.71  #Demod        : 3
% 2.47/1.71  #Tautology    : 1
% 2.47/1.71  #SimpNegUnit  : 0
% 2.47/1.71  #BackRed      : 0
% 2.47/1.71  
% 2.47/1.71  #Partial instantiations: 0
% 2.47/1.71  #Strategies tried      : 1
% 2.47/1.71  
% 2.47/1.71  Timing (in seconds)
% 2.47/1.71  ----------------------
% 2.47/1.72  Preprocessing        : 0.39
% 2.47/1.72  Parsing              : 0.22
% 2.47/1.72  CNF conversion       : 0.03
% 2.47/1.72  Main loop            : 0.41
% 2.47/1.72  Inferencing          : 0.14
% 2.47/1.72  Reduction            : 0.07
% 2.47/1.72  Demodulation         : 0.05
% 2.47/1.72  BG Simplification    : 0.02
% 2.47/1.72  Subsumption          : 0.16
% 2.47/1.72  Abstraction          : 0.01
% 2.47/1.72  MUC search           : 0.00
% 2.47/1.72  Cooper               : 0.00
% 2.47/1.72  Total                : 0.84
% 2.47/1.72  Index Insertion      : 0.00
% 2.47/1.72  Index Deletion       : 0.00
% 2.47/1.72  Index Matching       : 0.00
% 2.47/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------

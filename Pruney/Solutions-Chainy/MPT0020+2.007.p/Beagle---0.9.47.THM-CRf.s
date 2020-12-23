%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:32 EST 2020

% Result     : Theorem 1.88s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   29 (  36 expanded)
%              Number of leaves         :   14 (  18 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  52 expanded)
%              Number of equality atoms :    0 (   0 expanded)
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

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D) )
       => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_12,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_14,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_6,plain,(
    ! [A_7,B_8] : r1_tarski(A_7,k2_xboole_0(A_7,B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_21,plain,(
    ! [A_17,C_18,B_19] :
      ( r1_tarski(A_17,C_18)
      | ~ r1_tarski(B_19,C_18)
      | ~ r1_tarski(A_17,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_31,plain,(
    ! [A_17,A_7,B_8] :
      ( r1_tarski(A_17,k2_xboole_0(A_7,B_8))
      | ~ r1_tarski(A_17,A_7) ) ),
    inference(resolution,[status(thm)],[c_6,c_21])).

tff(c_72,plain,(
    ! [A_27,C_28,B_29] :
      ( r1_tarski(k2_xboole_0(A_27,C_28),B_29)
      | ~ r1_tarski(C_28,B_29)
      | ~ r1_tarski(A_27,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_10,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_3'),k2_xboole_0('#skF_2','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_103,plain,
    ( ~ r1_tarski('#skF_3',k2_xboole_0('#skF_2','#skF_4'))
    | ~ r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_4')) ),
    inference(resolution,[status(thm)],[c_72,c_10])).

tff(c_108,plain,(
    ~ r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_103])).

tff(c_111,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_31,c_108])).

tff(c_118,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_111])).

tff(c_119,plain,(
    ~ r1_tarski('#skF_3',k2_xboole_0('#skF_2','#skF_4')) ),
    inference(splitRight,[status(thm)],[c_103])).

tff(c_126,plain,(
    ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_2,c_119])).

tff(c_131,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 16:03:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.88/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.20  
% 1.88/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.20  %$ r1_tarski > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.88/1.20  
% 1.88/1.20  %Foreground sorts:
% 1.88/1.20  
% 1.88/1.20  
% 1.88/1.20  %Background operators:
% 1.88/1.20  
% 1.88/1.20  
% 1.88/1.20  %Foreground operators:
% 1.88/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.88/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.88/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.88/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.88/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.88/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.88/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.88/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.88/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.88/1.20  
% 1.92/1.21  tff(f_50, negated_conjecture, ~(![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_xboole_1)).
% 1.92/1.21  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.92/1.21  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.92/1.21  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_xboole_1)).
% 1.92/1.21  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t8_xboole_1)).
% 1.92/1.21  tff(c_12, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.92/1.21  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.92/1.21  tff(c_14, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.92/1.21  tff(c_6, plain, (![A_7, B_8]: (r1_tarski(A_7, k2_xboole_0(A_7, B_8)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.92/1.21  tff(c_21, plain, (![A_17, C_18, B_19]: (r1_tarski(A_17, C_18) | ~r1_tarski(B_19, C_18) | ~r1_tarski(A_17, B_19))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.21  tff(c_31, plain, (![A_17, A_7, B_8]: (r1_tarski(A_17, k2_xboole_0(A_7, B_8)) | ~r1_tarski(A_17, A_7))), inference(resolution, [status(thm)], [c_6, c_21])).
% 1.92/1.21  tff(c_72, plain, (![A_27, C_28, B_29]: (r1_tarski(k2_xboole_0(A_27, C_28), B_29) | ~r1_tarski(C_28, B_29) | ~r1_tarski(A_27, B_29))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.92/1.21  tff(c_10, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_3'), k2_xboole_0('#skF_2', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.92/1.21  tff(c_103, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_2', '#skF_4')) | ~r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_4'))), inference(resolution, [status(thm)], [c_72, c_10])).
% 1.92/1.21  tff(c_108, plain, (~r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_4'))), inference(splitLeft, [status(thm)], [c_103])).
% 1.92/1.21  tff(c_111, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_31, c_108])).
% 1.92/1.21  tff(c_118, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_111])).
% 1.92/1.21  tff(c_119, plain, (~r1_tarski('#skF_3', k2_xboole_0('#skF_2', '#skF_4'))), inference(splitRight, [status(thm)], [c_103])).
% 1.92/1.21  tff(c_126, plain, (~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_2, c_119])).
% 1.92/1.21  tff(c_131, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_126])).
% 1.92/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.21  
% 1.92/1.21  Inference rules
% 1.92/1.21  ----------------------
% 1.92/1.21  #Ref     : 0
% 1.92/1.21  #Sup     : 27
% 1.92/1.21  #Fact    : 0
% 1.92/1.21  #Define  : 0
% 1.92/1.21  #Split   : 2
% 1.92/1.21  #Chain   : 0
% 1.92/1.21  #Close   : 0
% 1.92/1.21  
% 1.92/1.21  Ordering : KBO
% 1.92/1.21  
% 1.92/1.21  Simplification rules
% 1.92/1.21  ----------------------
% 1.92/1.21  #Subsume      : 2
% 1.92/1.21  #Demod        : 5
% 1.92/1.21  #Tautology    : 1
% 1.92/1.21  #SimpNegUnit  : 0
% 1.92/1.21  #BackRed      : 0
% 1.92/1.21  
% 1.92/1.21  #Partial instantiations: 0
% 1.92/1.21  #Strategies tried      : 1
% 1.92/1.21  
% 1.92/1.21  Timing (in seconds)
% 1.92/1.21  ----------------------
% 1.92/1.22  Preprocessing        : 0.28
% 1.92/1.22  Parsing              : 0.15
% 1.92/1.22  CNF conversion       : 0.02
% 1.92/1.22  Main loop            : 0.16
% 1.92/1.22  Inferencing          : 0.06
% 1.92/1.22  Reduction            : 0.04
% 1.92/1.22  Demodulation         : 0.03
% 1.92/1.22  BG Simplification    : 0.01
% 1.92/1.22  Subsumption          : 0.04
% 1.92/1.22  Abstraction          : 0.01
% 1.92/1.22  MUC search           : 0.00
% 1.92/1.22  Cooper               : 0.00
% 1.92/1.22  Total                : 0.46
% 1.92/1.22  Index Insertion      : 0.00
% 1.92/1.22  Index Deletion       : 0.00
% 1.92/1.22  Index Matching       : 0.00
% 1.92/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------

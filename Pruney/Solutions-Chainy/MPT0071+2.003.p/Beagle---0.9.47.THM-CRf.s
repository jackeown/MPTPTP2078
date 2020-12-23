%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:24 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.88s
% Verified   : 
% Statistics : Number of formulae       :   25 (  31 expanded)
%              Number of leaves         :   12 (  17 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  51 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    1 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & r1_tarski(C,D)
          & r1_xboole_0(B,D) )
       => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_xboole_0(B,C) )
     => r1_xboole_0(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t63_xboole_1)).

tff(c_10,plain,(
    r1_tarski('#skF_3','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_12,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    r1_xboole_0('#skF_2','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_13,plain,(
    ! [B_6,A_7] :
      ( r1_xboole_0(B_6,A_7)
      | ~ r1_xboole_0(A_7,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_16,plain,(
    r1_xboole_0('#skF_4','#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_13])).

tff(c_4,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_xboole_0(A_3,C_5)
      | ~ r1_xboole_0(B_4,C_5)
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_35,plain,(
    ! [A_12] :
      ( r1_xboole_0(A_12,'#skF_2')
      | ~ r1_tarski(A_12,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_16,c_4])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_49,plain,(
    ! [A_14] :
      ( r1_xboole_0('#skF_2',A_14)
      | ~ r1_tarski(A_14,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_35,c_2])).

tff(c_86,plain,(
    ! [A_21,A_22] :
      ( r1_xboole_0(A_21,A_22)
      | ~ r1_tarski(A_21,'#skF_2')
      | ~ r1_tarski(A_22,'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_49,c_4])).

tff(c_6,plain,(
    ~ r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_93,plain,
    ( ~ r1_tarski('#skF_1','#skF_2')
    | ~ r1_tarski('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_86,c_6])).

tff(c_99,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_12,c_93])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 10:06:56 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.17  
% 1.61/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.61/1.17  %$ r1_xboole_0 > r1_tarski > #nlpp > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 1.61/1.17  
% 1.61/1.17  %Foreground sorts:
% 1.61/1.17  
% 1.61/1.17  
% 1.61/1.17  %Background operators:
% 1.61/1.17  
% 1.61/1.17  
% 1.61/1.17  %Foreground operators:
% 1.61/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.61/1.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.61/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.17  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.17  tff('#skF_4', type, '#skF_4': $i).
% 1.61/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.17  
% 1.88/1.18  tff(f_44, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & r1_tarski(C, D)) & r1_xboole_0(B, D)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_xboole_1)).
% 1.88/1.18  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.88/1.18  tff(f_35, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_xboole_0(B, C)) => r1_xboole_0(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t63_xboole_1)).
% 1.88/1.18  tff(c_10, plain, (r1_tarski('#skF_3', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.88/1.18  tff(c_12, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.88/1.18  tff(c_8, plain, (r1_xboole_0('#skF_2', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.88/1.18  tff(c_13, plain, (![B_6, A_7]: (r1_xboole_0(B_6, A_7) | ~r1_xboole_0(A_7, B_6))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.18  tff(c_16, plain, (r1_xboole_0('#skF_4', '#skF_2')), inference(resolution, [status(thm)], [c_8, c_13])).
% 1.88/1.18  tff(c_4, plain, (![A_3, C_5, B_4]: (r1_xboole_0(A_3, C_5) | ~r1_xboole_0(B_4, C_5) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.88/1.18  tff(c_35, plain, (![A_12]: (r1_xboole_0(A_12, '#skF_2') | ~r1_tarski(A_12, '#skF_4'))), inference(resolution, [status(thm)], [c_16, c_4])).
% 1.88/1.18  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.88/1.18  tff(c_49, plain, (![A_14]: (r1_xboole_0('#skF_2', A_14) | ~r1_tarski(A_14, '#skF_4'))), inference(resolution, [status(thm)], [c_35, c_2])).
% 1.88/1.18  tff(c_86, plain, (![A_21, A_22]: (r1_xboole_0(A_21, A_22) | ~r1_tarski(A_21, '#skF_2') | ~r1_tarski(A_22, '#skF_4'))), inference(resolution, [status(thm)], [c_49, c_4])).
% 1.88/1.18  tff(c_6, plain, (~r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.88/1.18  tff(c_93, plain, (~r1_tarski('#skF_1', '#skF_2') | ~r1_tarski('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_86, c_6])).
% 1.88/1.18  tff(c_99, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_12, c_93])).
% 1.88/1.18  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.18  
% 1.88/1.18  Inference rules
% 1.88/1.18  ----------------------
% 1.88/1.18  #Ref     : 0
% 1.88/1.18  #Sup     : 22
% 1.88/1.18  #Fact    : 0
% 1.88/1.18  #Define  : 0
% 1.88/1.18  #Split   : 5
% 1.88/1.18  #Chain   : 0
% 1.88/1.18  #Close   : 0
% 1.88/1.18  
% 1.88/1.18  Ordering : KBO
% 1.88/1.18  
% 1.88/1.18  Simplification rules
% 1.88/1.18  ----------------------
% 1.88/1.18  #Subsume      : 3
% 1.88/1.18  #Demod        : 3
% 1.88/1.18  #Tautology    : 1
% 1.88/1.18  #SimpNegUnit  : 0
% 1.88/1.18  #BackRed      : 0
% 1.88/1.18  
% 1.88/1.18  #Partial instantiations: 0
% 1.88/1.18  #Strategies tried      : 1
% 1.88/1.18  
% 1.88/1.18  Timing (in seconds)
% 1.88/1.18  ----------------------
% 1.88/1.19  Preprocessing        : 0.25
% 1.88/1.19  Parsing              : 0.14
% 1.88/1.19  CNF conversion       : 0.02
% 1.88/1.19  Main loop            : 0.16
% 1.88/1.19  Inferencing          : 0.06
% 1.88/1.19  Reduction            : 0.03
% 1.88/1.19  Demodulation         : 0.02
% 1.88/1.19  BG Simplification    : 0.01
% 1.88/1.19  Subsumption          : 0.05
% 1.88/1.19  Abstraction          : 0.01
% 1.88/1.19  MUC search           : 0.00
% 1.88/1.19  Cooper               : 0.00
% 1.88/1.19  Total                : 0.44
% 1.88/1.19  Index Insertion      : 0.00
% 1.88/1.19  Index Deletion       : 0.00
% 1.88/1.19  Index Matching       : 0.00
% 1.88/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

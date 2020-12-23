%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:42:30 EST 2020

% Result     : Theorem 3.46s
% Output     : CNFRefutation 3.46s
% Verified   : 
% Statistics : Number of formulae       :   35 (  42 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   43 (  59 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(A,B)
       => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_43,plain,(
    ! [D_27,B_28,A_29] :
      ( ~ r2_hidden(D_27,B_28)
      | r2_hidden(D_27,k2_xboole_0(A_29,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_1256,plain,(
    ! [A_179,A_180,B_181] :
      ( r1_tarski(A_179,k2_xboole_0(A_180,B_181))
      | ~ r2_hidden('#skF_1'(A_179,k2_xboole_0(A_180,B_181)),B_181) ) ),
    inference(resolution,[status(thm)],[c_43,c_4])).

tff(c_1284,plain,(
    ! [A_1,A_180] : r1_tarski(A_1,k2_xboole_0(A_180,A_1)) ),
    inference(resolution,[status(thm)],[c_6,c_1256])).

tff(c_34,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    ! [A_15,B_16] : r1_tarski(A_15,k2_xboole_0(A_15,B_16)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_66,plain,(
    ! [A_36,C_37,B_38] :
      ( r1_tarski(A_36,C_37)
      | ~ r1_tarski(B_38,C_37)
      | ~ r1_tarski(A_36,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_74,plain,(
    ! [A_36,A_15,B_16] :
      ( r1_tarski(A_36,k2_xboole_0(A_15,B_16))
      | ~ r1_tarski(A_36,A_15) ) ),
    inference(resolution,[status(thm)],[c_28,c_66])).

tff(c_124,plain,(
    ! [A_50,C_51,B_52] :
      ( r1_tarski(k2_xboole_0(A_50,C_51),B_52)
      | ~ r1_tarski(C_51,B_52)
      | ~ r1_tarski(A_50,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_32,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_4','#skF_6'),k2_xboole_0('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_151,plain,
    ( ~ r1_tarski('#skF_6',k2_xboole_0('#skF_5','#skF_6'))
    | ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_124,c_32])).

tff(c_156,plain,(
    ~ r1_tarski('#skF_4',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_151])).

tff(c_159,plain,(
    ~ r1_tarski('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_74,c_156])).

tff(c_163,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_159])).

tff(c_164,plain,(
    ~ r1_tarski('#skF_6',k2_xboole_0('#skF_5','#skF_6')) ),
    inference(splitRight,[status(thm)],[c_151])).

tff(c_1289,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1284,c_164])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 14:46:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.46/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.59  
% 3.46/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.59  %$ r2_hidden > r1_tarski > k2_xboole_0 > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 3.46/1.59  
% 3.46/1.59  %Foreground sorts:
% 3.46/1.59  
% 3.46/1.59  
% 3.46/1.59  %Background operators:
% 3.46/1.59  
% 3.46/1.59  
% 3.46/1.59  %Foreground operators:
% 3.46/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.46/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.46/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.46/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.46/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.46/1.59  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.46/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.46/1.59  tff('#skF_4', type, '#skF_4': $i).
% 3.46/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.46/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.46/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.46/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.46/1.59  
% 3.46/1.60  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.46/1.60  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 3.46/1.60  tff(f_60, negated_conjecture, ~(![A, B, C]: (r1_tarski(A, B) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_xboole_1)).
% 3.46/1.60  tff(f_49, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.46/1.60  tff(f_47, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 3.46/1.60  tff(f_55, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 3.46/1.60  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.46/1.60  tff(c_43, plain, (![D_27, B_28, A_29]: (~r2_hidden(D_27, B_28) | r2_hidden(D_27, k2_xboole_0(A_29, B_28)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.46/1.60  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.46/1.60  tff(c_1256, plain, (![A_179, A_180, B_181]: (r1_tarski(A_179, k2_xboole_0(A_180, B_181)) | ~r2_hidden('#skF_1'(A_179, k2_xboole_0(A_180, B_181)), B_181))), inference(resolution, [status(thm)], [c_43, c_4])).
% 3.46/1.60  tff(c_1284, plain, (![A_1, A_180]: (r1_tarski(A_1, k2_xboole_0(A_180, A_1)))), inference(resolution, [status(thm)], [c_6, c_1256])).
% 3.46/1.60  tff(c_34, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.46/1.60  tff(c_28, plain, (![A_15, B_16]: (r1_tarski(A_15, k2_xboole_0(A_15, B_16)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.46/1.60  tff(c_66, plain, (![A_36, C_37, B_38]: (r1_tarski(A_36, C_37) | ~r1_tarski(B_38, C_37) | ~r1_tarski(A_36, B_38))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.46/1.60  tff(c_74, plain, (![A_36, A_15, B_16]: (r1_tarski(A_36, k2_xboole_0(A_15, B_16)) | ~r1_tarski(A_36, A_15))), inference(resolution, [status(thm)], [c_28, c_66])).
% 3.46/1.60  tff(c_124, plain, (![A_50, C_51, B_52]: (r1_tarski(k2_xboole_0(A_50, C_51), B_52) | ~r1_tarski(C_51, B_52) | ~r1_tarski(A_50, B_52))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.46/1.60  tff(c_32, plain, (~r1_tarski(k2_xboole_0('#skF_4', '#skF_6'), k2_xboole_0('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.46/1.60  tff(c_151, plain, (~r1_tarski('#skF_6', k2_xboole_0('#skF_5', '#skF_6')) | ~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_124, c_32])).
% 3.46/1.60  tff(c_156, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitLeft, [status(thm)], [c_151])).
% 3.46/1.60  tff(c_159, plain, (~r1_tarski('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_74, c_156])).
% 3.46/1.60  tff(c_163, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_159])).
% 3.46/1.60  tff(c_164, plain, (~r1_tarski('#skF_6', k2_xboole_0('#skF_5', '#skF_6'))), inference(splitRight, [status(thm)], [c_151])).
% 3.46/1.60  tff(c_1289, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1284, c_164])).
% 3.46/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.46/1.60  
% 3.46/1.60  Inference rules
% 3.46/1.60  ----------------------
% 3.46/1.60  #Ref     : 0
% 3.46/1.60  #Sup     : 302
% 3.46/1.60  #Fact    : 6
% 3.46/1.60  #Define  : 0
% 3.46/1.60  #Split   : 6
% 3.46/1.60  #Chain   : 0
% 3.46/1.60  #Close   : 0
% 3.46/1.60  
% 3.46/1.60  Ordering : KBO
% 3.46/1.60  
% 3.46/1.60  Simplification rules
% 3.46/1.60  ----------------------
% 3.46/1.60  #Subsume      : 79
% 3.46/1.60  #Demod        : 24
% 3.46/1.60  #Tautology    : 24
% 3.46/1.60  #SimpNegUnit  : 0
% 3.46/1.60  #BackRed      : 1
% 3.46/1.60  
% 3.46/1.60  #Partial instantiations: 0
% 3.46/1.60  #Strategies tried      : 1
% 3.46/1.60  
% 3.46/1.60  Timing (in seconds)
% 3.46/1.60  ----------------------
% 3.46/1.60  Preprocessing        : 0.28
% 3.46/1.60  Parsing              : 0.15
% 3.46/1.60  CNF conversion       : 0.02
% 3.46/1.60  Main loop            : 0.55
% 3.46/1.60  Inferencing          : 0.18
% 3.46/1.60  Reduction            : 0.14
% 3.46/1.60  Demodulation         : 0.10
% 3.46/1.60  BG Simplification    : 0.03
% 3.46/1.60  Subsumption          : 0.16
% 3.46/1.60  Abstraction          : 0.03
% 3.46/1.60  MUC search           : 0.00
% 3.46/1.60  Cooper               : 0.00
% 3.46/1.60  Total                : 0.85
% 3.46/1.60  Index Insertion      : 0.00
% 3.46/1.60  Index Deletion       : 0.00
% 3.46/1.60  Index Matching       : 0.00
% 3.46/1.60  BG Taut test         : 0.00
%------------------------------------------------------------------------------

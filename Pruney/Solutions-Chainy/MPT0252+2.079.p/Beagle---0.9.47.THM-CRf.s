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
% DateTime   : Thu Dec  3 09:51:10 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   36 (  43 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   36 (  52 expanded)
%              Number of equality atoms :    8 (  12 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_50,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_32,plain,(
    ! [D_17,B_13] : r2_hidden(D_17,k2_tarski(D_17,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_24,plain,(
    ! [B_8] : r1_tarski(B_8,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,k2_xboole_0(C_11,B_10))
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_52,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_75,plain,(
    ! [B_31,A_32] :
      ( B_31 = A_32
      | ~ r1_tarski(B_31,A_32)
      | ~ r1_tarski(A_32,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_80,plain,
    ( k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = '#skF_7'
    | ~ r1_tarski('#skF_7',k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7')) ),
    inference(resolution,[status(thm)],[c_52,c_75])).

tff(c_89,plain,(
    ~ r1_tarski('#skF_7',k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_80])).

tff(c_92,plain,(
    ~ r1_tarski('#skF_7','#skF_7') ),
    inference(resolution,[status(thm)],[c_26,c_89])).

tff(c_96,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_92])).

tff(c_97,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_80])).

tff(c_113,plain,(
    ! [D_39,A_40,B_41] :
      ( ~ r2_hidden(D_39,A_40)
      | r2_hidden(D_39,k2_xboole_0(A_40,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_128,plain,(
    ! [D_45] :
      ( ~ r2_hidden(D_45,k2_tarski('#skF_5','#skF_6'))
      | r2_hidden(D_45,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_113])).

tff(c_136,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_32,c_128])).

tff(c_141,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_136])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 10:14:37 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.25  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.25  
% 1.90/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.25  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.90/1.25  
% 1.90/1.25  %Foreground sorts:
% 1.90/1.25  
% 1.90/1.25  
% 1.90/1.25  %Background operators:
% 1.90/1.25  
% 1.90/1.25  
% 1.90/1.25  %Foreground operators:
% 1.90/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.90/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.25  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.90/1.25  tff('#skF_7', type, '#skF_7': $i).
% 1.90/1.25  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.25  tff('#skF_5', type, '#skF_5': $i).
% 1.90/1.25  tff('#skF_6', type, '#skF_6': $i).
% 1.90/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.90/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.90/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.25  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.90/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.90/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.90/1.25  
% 1.90/1.26  tff(f_62, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 1.90/1.26  tff(f_53, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.90/1.26  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 1.90/1.26  tff(f_44, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.90/1.26  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.90/1.26  tff(c_50, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.90/1.26  tff(c_32, plain, (![D_17, B_13]: (r2_hidden(D_17, k2_tarski(D_17, B_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.90/1.26  tff(c_24, plain, (![B_8]: (r1_tarski(B_8, B_8))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.90/1.26  tff(c_26, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, k2_xboole_0(C_11, B_10)) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.90/1.26  tff(c_52, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.90/1.26  tff(c_75, plain, (![B_31, A_32]: (B_31=A_32 | ~r1_tarski(B_31, A_32) | ~r1_tarski(A_32, B_31))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.90/1.26  tff(c_80, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')='#skF_7' | ~r1_tarski('#skF_7', k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7'))), inference(resolution, [status(thm)], [c_52, c_75])).
% 1.90/1.26  tff(c_89, plain, (~r1_tarski('#skF_7', k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7'))), inference(splitLeft, [status(thm)], [c_80])).
% 1.90/1.26  tff(c_92, plain, (~r1_tarski('#skF_7', '#skF_7')), inference(resolution, [status(thm)], [c_26, c_89])).
% 1.90/1.26  tff(c_96, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_24, c_92])).
% 1.90/1.26  tff(c_97, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')='#skF_7'), inference(splitRight, [status(thm)], [c_80])).
% 1.90/1.26  tff(c_113, plain, (![D_39, A_40, B_41]: (~r2_hidden(D_39, A_40) | r2_hidden(D_39, k2_xboole_0(A_40, B_41)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.90/1.26  tff(c_128, plain, (![D_45]: (~r2_hidden(D_45, k2_tarski('#skF_5', '#skF_6')) | r2_hidden(D_45, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_97, c_113])).
% 1.90/1.26  tff(c_136, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_32, c_128])).
% 1.90/1.26  tff(c_141, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_136])).
% 1.90/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.90/1.26  
% 1.90/1.26  Inference rules
% 1.90/1.26  ----------------------
% 1.90/1.26  #Ref     : 0
% 1.90/1.26  #Sup     : 17
% 1.90/1.26  #Fact    : 0
% 1.90/1.26  #Define  : 0
% 1.90/1.26  #Split   : 1
% 1.90/1.26  #Chain   : 0
% 1.90/1.26  #Close   : 0
% 1.90/1.26  
% 1.90/1.26  Ordering : KBO
% 1.90/1.26  
% 1.90/1.26  Simplification rules
% 1.90/1.26  ----------------------
% 1.90/1.26  #Subsume      : 0
% 1.90/1.26  #Demod        : 7
% 1.90/1.26  #Tautology    : 14
% 1.90/1.26  #SimpNegUnit  : 1
% 1.90/1.26  #BackRed      : 1
% 1.90/1.26  
% 1.90/1.26  #Partial instantiations: 0
% 1.90/1.26  #Strategies tried      : 1
% 1.90/1.26  
% 1.90/1.26  Timing (in seconds)
% 1.90/1.26  ----------------------
% 1.90/1.26  Preprocessing        : 0.32
% 1.90/1.26  Parsing              : 0.16
% 1.90/1.26  CNF conversion       : 0.02
% 1.90/1.26  Main loop            : 0.12
% 1.90/1.27  Inferencing          : 0.03
% 1.90/1.27  Reduction            : 0.04
% 1.90/1.27  Demodulation         : 0.03
% 1.90/1.27  BG Simplification    : 0.01
% 1.90/1.27  Subsumption          : 0.03
% 1.90/1.27  Abstraction          : 0.01
% 1.90/1.27  MUC search           : 0.00
% 1.90/1.27  Cooper               : 0.00
% 1.90/1.27  Total                : 0.46
% 1.90/1.27  Index Insertion      : 0.00
% 1.90/1.27  Index Deletion       : 0.00
% 1.90/1.27  Index Matching       : 0.00
% 1.90/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:10 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   27 (  28 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  26 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_xboole_0(k2_tarski(A,B),C)
          & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_44,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_30,plain,(
    ! [D_16,B_12] : r2_hidden(D_16,k2_tarski(D_16,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_46,plain,(
    r1_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_53,plain,(
    ! [A_23,B_24] :
      ( k4_xboole_0(A_23,B_24) = A_23
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_57,plain,(
    k4_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_53])).

tff(c_90,plain,(
    ! [D_29,B_30,A_31] :
      ( ~ r2_hidden(D_29,B_30)
      | ~ r2_hidden(D_29,k4_xboole_0(A_31,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_113,plain,(
    ! [D_37] :
      ( ~ r2_hidden(D_37,'#skF_7')
      | ~ r2_hidden(D_37,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_90])).

tff(c_121,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_30,c_113])).

tff(c_126,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_121])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n010.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 12:25:44 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.16  
% 1.79/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.16  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k2_tarski > #nlpp > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.79/1.16  
% 1.79/1.16  %Foreground sorts:
% 1.79/1.16  
% 1.79/1.16  
% 1.79/1.16  %Background operators:
% 1.79/1.16  
% 1.79/1.16  
% 1.79/1.16  %Foreground operators:
% 1.79/1.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.79/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.79/1.16  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.79/1.16  tff('#skF_7', type, '#skF_7': $i).
% 1.79/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.79/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.79/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.79/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.79/1.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.79/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.79/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.16  
% 1.79/1.16  tff(f_58, negated_conjecture, ~(![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 1.79/1.16  tff(f_52, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.79/1.16  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.79/1.16  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.79/1.16  tff(c_44, plain, (r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.79/1.16  tff(c_30, plain, (![D_16, B_12]: (r2_hidden(D_16, k2_tarski(D_16, B_12)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.79/1.16  tff(c_46, plain, (r1_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.79/1.16  tff(c_53, plain, (![A_23, B_24]: (k4_xboole_0(A_23, B_24)=A_23 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.79/1.16  tff(c_57, plain, (k4_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_46, c_53])).
% 1.79/1.16  tff(c_90, plain, (![D_29, B_30, A_31]: (~r2_hidden(D_29, B_30) | ~r2_hidden(D_29, k4_xboole_0(A_31, B_30)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.79/1.16  tff(c_113, plain, (![D_37]: (~r2_hidden(D_37, '#skF_7') | ~r2_hidden(D_37, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_57, c_90])).
% 1.79/1.16  tff(c_121, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_30, c_113])).
% 1.79/1.16  tff(c_126, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_121])).
% 1.79/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.16  
% 1.79/1.16  Inference rules
% 1.79/1.16  ----------------------
% 1.79/1.16  #Ref     : 0
% 1.79/1.16  #Sup     : 20
% 1.79/1.16  #Fact    : 0
% 1.79/1.16  #Define  : 0
% 1.79/1.16  #Split   : 0
% 1.79/1.16  #Chain   : 0
% 1.79/1.16  #Close   : 0
% 1.79/1.16  
% 1.79/1.16  Ordering : KBO
% 1.79/1.16  
% 1.79/1.16  Simplification rules
% 1.79/1.16  ----------------------
% 1.79/1.16  #Subsume      : 1
% 1.79/1.16  #Demod        : 4
% 1.79/1.16  #Tautology    : 10
% 1.79/1.16  #SimpNegUnit  : 0
% 1.79/1.16  #BackRed      : 0
% 1.79/1.16  
% 1.79/1.16  #Partial instantiations: 0
% 1.79/1.16  #Strategies tried      : 1
% 1.79/1.16  
% 1.79/1.16  Timing (in seconds)
% 1.79/1.16  ----------------------
% 1.79/1.17  Preprocessing        : 0.28
% 1.79/1.17  Parsing              : 0.14
% 1.79/1.17  CNF conversion       : 0.02
% 1.79/1.17  Main loop            : 0.13
% 1.79/1.17  Inferencing          : 0.04
% 1.79/1.17  Reduction            : 0.04
% 1.79/1.17  Demodulation         : 0.03
% 1.79/1.17  BG Simplification    : 0.02
% 1.79/1.17  Subsumption          : 0.03
% 1.79/1.17  Abstraction          : 0.01
% 1.79/1.17  MUC search           : 0.00
% 1.79/1.17  Cooper               : 0.00
% 1.79/1.17  Total                : 0.43
% 1.79/1.17  Index Insertion      : 0.00
% 1.79/1.17  Index Deletion       : 0.00
% 1.79/1.17  Index Matching       : 0.00
% 1.79/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------

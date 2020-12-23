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
% DateTime   : Thu Dec  3 09:51:04 EST 2020

% Result     : Theorem 1.90s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   31 (  34 expanded)
%              Number of leaves         :   19 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   29 (  33 expanded)
%              Number of equality atoms :    5 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_32,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_35,plain,(
    r1_tarski(k2_xboole_0('#skF_6',k2_tarski('#skF_4','#skF_5')),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34])).

tff(c_79,plain,(
    ! [A_30,C_31,B_32] :
      ( r1_tarski(A_30,C_31)
      | ~ r1_tarski(k2_xboole_0(A_30,B_32),C_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_253,plain,(
    ! [B_60,C_61,A_62] :
      ( r1_tarski(B_60,C_61)
      | ~ r1_tarski(k2_xboole_0(A_62,B_60),C_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_79])).

tff(c_301,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_35,c_253])).

tff(c_16,plain,(
    ! [D_16,B_12] : r2_hidden(D_16,k2_tarski(D_16,B_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_174,plain,(
    ! [C_45,B_46,A_47] :
      ( r2_hidden(C_45,B_46)
      | ~ r2_hidden(C_45,A_47)
      | ~ r1_tarski(A_47,B_46) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_302,plain,(
    ! [D_63,B_64,B_65] :
      ( r2_hidden(D_63,B_64)
      | ~ r1_tarski(k2_tarski(D_63,B_65),B_64) ) ),
    inference(resolution,[status(thm)],[c_16,c_174])).

tff(c_305,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_301,c_302])).

tff(c_337,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_305])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n007.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 12:01:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.90/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.22  
% 1.90/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.23  %$ r2_hidden > r1_tarski > k2_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.90/1.23  
% 1.90/1.23  %Foreground sorts:
% 1.90/1.23  
% 1.90/1.23  
% 1.90/1.23  %Background operators:
% 1.90/1.23  
% 1.90/1.23  
% 1.90/1.23  %Foreground operators:
% 1.90/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.90/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.23  tff('#skF_5', type, '#skF_5': $i).
% 1.90/1.23  tff('#skF_6', type, '#skF_6': $i).
% 1.90/1.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.90/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.23  tff('#skF_4', type, '#skF_4': $i).
% 1.90/1.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.90/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.90/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.90/1.23  
% 2.09/1.24  tff(f_54, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 2.09/1.24  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.09/1.24  tff(f_38, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 2.09/1.24  tff(f_47, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.09/1.24  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 2.09/1.24  tff(c_32, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.09/1.24  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.09/1.24  tff(c_34, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.09/1.24  tff(c_35, plain, (r1_tarski(k2_xboole_0('#skF_6', k2_tarski('#skF_4', '#skF_5')), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_34])).
% 2.09/1.24  tff(c_79, plain, (![A_30, C_31, B_32]: (r1_tarski(A_30, C_31) | ~r1_tarski(k2_xboole_0(A_30, B_32), C_31))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.09/1.24  tff(c_253, plain, (![B_60, C_61, A_62]: (r1_tarski(B_60, C_61) | ~r1_tarski(k2_xboole_0(A_62, B_60), C_61))), inference(superposition, [status(thm), theory('equality')], [c_2, c_79])).
% 2.09/1.24  tff(c_301, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(resolution, [status(thm)], [c_35, c_253])).
% 2.09/1.24  tff(c_16, plain, (![D_16, B_12]: (r2_hidden(D_16, k2_tarski(D_16, B_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.09/1.24  tff(c_174, plain, (![C_45, B_46, A_47]: (r2_hidden(C_45, B_46) | ~r2_hidden(C_45, A_47) | ~r1_tarski(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.09/1.24  tff(c_302, plain, (![D_63, B_64, B_65]: (r2_hidden(D_63, B_64) | ~r1_tarski(k2_tarski(D_63, B_65), B_64))), inference(resolution, [status(thm)], [c_16, c_174])).
% 2.09/1.24  tff(c_305, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_301, c_302])).
% 2.09/1.24  tff(c_337, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_305])).
% 2.09/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.24  
% 2.09/1.24  Inference rules
% 2.09/1.24  ----------------------
% 2.09/1.24  #Ref     : 0
% 2.09/1.24  #Sup     : 65
% 2.09/1.24  #Fact    : 0
% 2.09/1.24  #Define  : 0
% 2.09/1.24  #Split   : 0
% 2.09/1.24  #Chain   : 0
% 2.09/1.24  #Close   : 0
% 2.09/1.24  
% 2.09/1.24  Ordering : KBO
% 2.09/1.24  
% 2.09/1.24  Simplification rules
% 2.09/1.24  ----------------------
% 2.09/1.24  #Subsume      : 2
% 2.09/1.24  #Demod        : 22
% 2.09/1.24  #Tautology    : 33
% 2.09/1.24  #SimpNegUnit  : 1
% 2.09/1.24  #BackRed      : 0
% 2.09/1.24  
% 2.09/1.24  #Partial instantiations: 0
% 2.09/1.24  #Strategies tried      : 1
% 2.09/1.24  
% 2.09/1.24  Timing (in seconds)
% 2.09/1.24  ----------------------
% 2.09/1.24  Preprocessing        : 0.29
% 2.09/1.24  Parsing              : 0.15
% 2.09/1.24  CNF conversion       : 0.02
% 2.09/1.24  Main loop            : 0.18
% 2.09/1.24  Inferencing          : 0.06
% 2.09/1.24  Reduction            : 0.07
% 2.09/1.24  Demodulation         : 0.06
% 2.09/1.24  BG Simplification    : 0.01
% 2.09/1.24  Subsumption          : 0.03
% 2.09/1.24  Abstraction          : 0.01
% 2.09/1.24  MUC search           : 0.00
% 2.09/1.24  Cooper               : 0.00
% 2.09/1.24  Total                : 0.49
% 2.09/1.24  Index Insertion      : 0.00
% 2.09/1.24  Index Deletion       : 0.00
% 2.09/1.24  Index Matching       : 0.00
% 2.09/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------

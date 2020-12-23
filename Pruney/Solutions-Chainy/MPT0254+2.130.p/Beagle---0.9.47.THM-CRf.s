%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:35 EST 2020

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   33 (  33 expanded)
%              Number of leaves         :   22 (  22 expanded)
%              Depth                    :    4
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :    8 (   8 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_36,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_40,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_57,plain,(
    ! [D_21,B_22] : r2_hidden(D_21,k2_tarski(D_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_60,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_57])).

tff(c_20,plain,(
    ! [A_7] : r1_xboole_0(A_7,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_80,plain,(
    ! [A_28,B_29] :
      ( ~ r2_hidden(A_28,B_29)
      | ~ r1_xboole_0(k1_tarski(A_28),B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_85,plain,(
    ! [A_28] : ~ r2_hidden(A_28,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_20,c_80])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_93,plain,(
    ! [D_35,A_36,B_37] :
      ( ~ r2_hidden(D_35,A_36)
      | r2_hidden(D_35,k2_xboole_0(A_36,B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_96,plain,(
    ! [D_35] :
      ( ~ r2_hidden(D_35,k1_tarski('#skF_5'))
      | r2_hidden(D_35,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_93])).

tff(c_98,plain,(
    ! [D_38] : ~ r2_hidden(D_38,k1_tarski('#skF_5')) ),
    inference(negUnitSimplification,[status(thm)],[c_85,c_96])).

tff(c_103,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_60,c_98])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n022.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 20:00:25 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.12  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.69/1.13  
% 1.69/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.13  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.79/1.13  
% 1.79/1.13  %Foreground sorts:
% 1.79/1.13  
% 1.79/1.13  
% 1.79/1.13  %Background operators:
% 1.79/1.13  
% 1.79/1.13  
% 1.79/1.13  %Foreground operators:
% 1.79/1.13  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.79/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.79/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.79/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.13  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.79/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.79/1.13  tff('#skF_5', type, '#skF_5': $i).
% 1.79/1.13  tff('#skF_6', type, '#skF_6': $i).
% 1.79/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.79/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.79/1.13  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.79/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.13  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.79/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.79/1.13  
% 1.79/1.14  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.79/1.14  tff(f_45, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.79/1.14  tff(f_36, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.79/1.14  tff(f_54, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.79/1.14  tff(f_58, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.79/1.14  tff(f_34, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.79/1.14  tff(c_40, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.79/1.14  tff(c_57, plain, (![D_21, B_22]: (r2_hidden(D_21, k2_tarski(D_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.79/1.14  tff(c_60, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_57])).
% 1.79/1.14  tff(c_20, plain, (![A_7]: (r1_xboole_0(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.79/1.14  tff(c_80, plain, (![A_28, B_29]: (~r2_hidden(A_28, B_29) | ~r1_xboole_0(k1_tarski(A_28), B_29))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.79/1.14  tff(c_85, plain, (![A_28]: (~r2_hidden(A_28, k1_xboole_0))), inference(resolution, [status(thm)], [c_20, c_80])).
% 1.79/1.14  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.79/1.14  tff(c_93, plain, (![D_35, A_36, B_37]: (~r2_hidden(D_35, A_36) | r2_hidden(D_35, k2_xboole_0(A_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.79/1.14  tff(c_96, plain, (![D_35]: (~r2_hidden(D_35, k1_tarski('#skF_5')) | r2_hidden(D_35, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_46, c_93])).
% 1.79/1.14  tff(c_98, plain, (![D_38]: (~r2_hidden(D_38, k1_tarski('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_85, c_96])).
% 1.79/1.14  tff(c_103, plain, $false, inference(resolution, [status(thm)], [c_60, c_98])).
% 1.79/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.14  
% 1.79/1.14  Inference rules
% 1.79/1.14  ----------------------
% 1.79/1.14  #Ref     : 0
% 1.79/1.14  #Sup     : 12
% 1.79/1.14  #Fact    : 0
% 1.79/1.14  #Define  : 0
% 1.79/1.14  #Split   : 0
% 1.79/1.14  #Chain   : 0
% 1.79/1.14  #Close   : 0
% 1.79/1.14  
% 1.79/1.14  Ordering : KBO
% 1.79/1.14  
% 1.79/1.14  Simplification rules
% 1.79/1.14  ----------------------
% 1.79/1.14  #Subsume      : 0
% 1.79/1.14  #Demod        : 1
% 1.79/1.14  #Tautology    : 7
% 1.79/1.14  #SimpNegUnit  : 2
% 1.79/1.14  #BackRed      : 0
% 1.79/1.14  
% 1.79/1.14  #Partial instantiations: 0
% 1.79/1.14  #Strategies tried      : 1
% 1.79/1.14  
% 1.79/1.14  Timing (in seconds)
% 1.79/1.14  ----------------------
% 1.79/1.14  Preprocessing        : 0.28
% 1.79/1.14  Parsing              : 0.14
% 1.79/1.14  CNF conversion       : 0.02
% 1.79/1.14  Main loop            : 0.10
% 1.79/1.14  Inferencing          : 0.03
% 1.79/1.14  Reduction            : 0.04
% 1.79/1.14  Demodulation         : 0.03
% 1.79/1.14  BG Simplification    : 0.01
% 1.79/1.14  Subsumption          : 0.02
% 1.79/1.14  Abstraction          : 0.01
% 1.79/1.14  MUC search           : 0.00
% 1.79/1.14  Cooper               : 0.00
% 1.79/1.14  Total                : 0.41
% 1.79/1.14  Index Insertion      : 0.00
% 1.79/1.14  Index Deletion       : 0.00
% 1.79/1.14  Index Matching       : 0.00
% 1.79/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------

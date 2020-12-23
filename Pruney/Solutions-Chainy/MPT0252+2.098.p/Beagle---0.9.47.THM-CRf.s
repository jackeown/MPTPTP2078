%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:13 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  42 expanded)
%              Number of equality atoms :    1 (   1 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_xboole_0(k2_tarski(A,B),C),C)
       => r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t47_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            | r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_xboole_0)).

tff(c_36,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_72,plain,(
    ! [A_37,B_38] :
      ( r2_hidden('#skF_1'(A_37,B_38),A_37)
      | r1_tarski(A_37,B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_78,plain,(
    ! [A_39] : r1_tarski(A_39,A_39) ),
    inference(resolution,[status(thm)],[c_72,c_4])).

tff(c_34,plain,(
    ! [A_16,C_18,B_17] :
      ( r2_hidden(A_16,C_18)
      | ~ r1_tarski(k2_tarski(A_16,B_17),C_18) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_87,plain,(
    ! [A_16,B_17] : r2_hidden(A_16,k2_tarski(A_16,B_17)) ),
    inference(resolution,[status(thm)],[c_78,c_34])).

tff(c_38,plain,(
    r1_tarski(k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_12,plain,(
    ! [D_11,A_6,B_7] :
      ( ~ r2_hidden(D_11,A_6)
      | r2_hidden(D_11,k2_xboole_0(A_6,B_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_91,plain,(
    ! [C_44,B_45,A_46] :
      ( r2_hidden(C_44,B_45)
      | ~ r2_hidden(C_44,A_46)
      | ~ r1_tarski(A_46,B_45) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_138,plain,(
    ! [D_57,B_58,A_59,B_60] :
      ( r2_hidden(D_57,B_58)
      | ~ r1_tarski(k2_xboole_0(A_59,B_60),B_58)
      | ~ r2_hidden(D_57,A_59) ) ),
    inference(resolution,[status(thm)],[c_12,c_91])).

tff(c_146,plain,(
    ! [D_61] :
      ( r2_hidden(D_61,'#skF_6')
      | ~ r2_hidden(D_61,k2_tarski('#skF_4','#skF_5')) ) ),
    inference(resolution,[status(thm)],[c_38,c_138])).

tff(c_154,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_87,c_146])).

tff(c_163,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_154])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n013.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:55:39 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.31  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.31  
% 1.99/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.32  %$ r2_hidden > r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.99/1.32  
% 1.99/1.32  %Foreground sorts:
% 1.99/1.32  
% 1.99/1.32  
% 1.99/1.32  %Background operators:
% 1.99/1.32  
% 1.99/1.32  
% 1.99/1.32  %Foreground operators:
% 1.99/1.32  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.32  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.32  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.99/1.32  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.32  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.32  tff('#skF_6', type, '#skF_6': $i).
% 1.99/1.32  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.32  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.99/1.32  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.32  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.99/1.32  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.32  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.99/1.32  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.32  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.99/1.32  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.99/1.32  
% 1.99/1.32  tff(f_56, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_xboole_0(k2_tarski(A, B), C), C) => r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t47_zfmisc_1)).
% 1.99/1.32  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 1.99/1.32  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.99/1.32  tff(f_41, axiom, (![A, B, C]: ((C = k2_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) | r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_xboole_0)).
% 1.99/1.32  tff(c_36, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.32  tff(c_72, plain, (![A_37, B_38]: (r2_hidden('#skF_1'(A_37, B_38), A_37) | r1_tarski(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.99/1.32  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.99/1.32  tff(c_78, plain, (![A_39]: (r1_tarski(A_39, A_39))), inference(resolution, [status(thm)], [c_72, c_4])).
% 1.99/1.32  tff(c_34, plain, (![A_16, C_18, B_17]: (r2_hidden(A_16, C_18) | ~r1_tarski(k2_tarski(A_16, B_17), C_18))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.99/1.32  tff(c_87, plain, (![A_16, B_17]: (r2_hidden(A_16, k2_tarski(A_16, B_17)))), inference(resolution, [status(thm)], [c_78, c_34])).
% 1.99/1.32  tff(c_38, plain, (r1_tarski(k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.99/1.32  tff(c_12, plain, (![D_11, A_6, B_7]: (~r2_hidden(D_11, A_6) | r2_hidden(D_11, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.99/1.32  tff(c_91, plain, (![C_44, B_45, A_46]: (r2_hidden(C_44, B_45) | ~r2_hidden(C_44, A_46) | ~r1_tarski(A_46, B_45))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.99/1.32  tff(c_138, plain, (![D_57, B_58, A_59, B_60]: (r2_hidden(D_57, B_58) | ~r1_tarski(k2_xboole_0(A_59, B_60), B_58) | ~r2_hidden(D_57, A_59))), inference(resolution, [status(thm)], [c_12, c_91])).
% 1.99/1.32  tff(c_146, plain, (![D_61]: (r2_hidden(D_61, '#skF_6') | ~r2_hidden(D_61, k2_tarski('#skF_4', '#skF_5')))), inference(resolution, [status(thm)], [c_38, c_138])).
% 1.99/1.32  tff(c_154, plain, (r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_87, c_146])).
% 1.99/1.32  tff(c_163, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_154])).
% 1.99/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.32  
% 1.99/1.32  Inference rules
% 1.99/1.32  ----------------------
% 1.99/1.32  #Ref     : 0
% 1.99/1.32  #Sup     : 26
% 1.99/1.32  #Fact    : 0
% 1.99/1.32  #Define  : 0
% 1.99/1.32  #Split   : 0
% 1.99/1.32  #Chain   : 0
% 1.99/1.32  #Close   : 0
% 1.99/1.32  
% 1.99/1.32  Ordering : KBO
% 1.99/1.32  
% 1.99/1.32  Simplification rules
% 1.99/1.32  ----------------------
% 1.99/1.32  #Subsume      : 4
% 1.99/1.32  #Demod        : 0
% 1.99/1.32  #Tautology    : 9
% 1.99/1.32  #SimpNegUnit  : 1
% 1.99/1.32  #BackRed      : 0
% 1.99/1.32  
% 1.99/1.32  #Partial instantiations: 0
% 1.99/1.32  #Strategies tried      : 1
% 1.99/1.32  
% 1.99/1.32  Timing (in seconds)
% 1.99/1.32  ----------------------
% 1.99/1.33  Preprocessing        : 0.41
% 1.99/1.33  Parsing              : 0.16
% 1.99/1.33  CNF conversion       : 0.05
% 1.99/1.33  Main loop            : 0.16
% 1.99/1.33  Inferencing          : 0.05
% 1.99/1.33  Reduction            : 0.05
% 1.99/1.33  Demodulation         : 0.03
% 1.99/1.33  BG Simplification    : 0.02
% 1.99/1.33  Subsumption          : 0.04
% 1.99/1.33  Abstraction          : 0.02
% 1.99/1.33  MUC search           : 0.00
% 1.99/1.33  Cooper               : 0.00
% 1.99/1.33  Total                : 0.60
% 1.99/1.33  Index Insertion      : 0.00
% 1.99/1.33  Index Deletion       : 0.00
% 1.99/1.33  Index Matching       : 0.00
% 1.99/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------

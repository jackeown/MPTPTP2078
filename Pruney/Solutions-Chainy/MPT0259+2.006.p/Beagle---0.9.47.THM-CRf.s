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
% DateTime   : Thu Dec  3 09:52:09 EST 2020

% Result     : Theorem 1.84s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   26 (  27 expanded)
%              Number of leaves         :   17 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   25 (  27 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( r1_xboole_0(k1_tarski(A),B)
          & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t54_zfmisc_1)).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(c_30,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_26,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    ! [D_16,B_17] : r2_hidden(D_16,k2_tarski(D_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_45,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_42])).

tff(c_32,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_63,plain,(
    ! [A_27,B_28,C_29] :
      ( ~ r1_xboole_0(A_27,B_28)
      | ~ r2_hidden(C_29,B_28)
      | ~ r2_hidden(C_29,A_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_67,plain,(
    ! [C_30] :
      ( ~ r2_hidden(C_30,'#skF_5')
      | ~ r2_hidden(C_30,k1_tarski('#skF_4')) ) ),
    inference(resolution,[status(thm)],[c_32,c_63])).

tff(c_79,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(resolution,[status(thm)],[c_45,c_67])).

tff(c_85,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_79])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n020.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 13:57:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.84/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.25  
% 1.89/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.25  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.89/1.25  
% 1.89/1.25  %Foreground sorts:
% 1.89/1.25  
% 1.89/1.25  
% 1.89/1.25  %Background operators:
% 1.89/1.25  
% 1.89/1.25  
% 1.89/1.25  %Foreground operators:
% 1.89/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.25  tff('#skF_5', type, '#skF_5': $i).
% 1.89/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.25  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.89/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.89/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.25  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.89/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.25  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.89/1.25  
% 1.89/1.26  tff(f_62, negated_conjecture, ~(![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t54_zfmisc_1)).
% 1.89/1.26  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.89/1.26  tff(f_52, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.89/1.26  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 1.89/1.26  tff(c_30, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.89/1.26  tff(c_26, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.89/1.26  tff(c_42, plain, (![D_16, B_17]: (r2_hidden(D_16, k2_tarski(D_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.89/1.26  tff(c_45, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_42])).
% 1.89/1.26  tff(c_32, plain, (r1_xboole_0(k1_tarski('#skF_4'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.89/1.26  tff(c_63, plain, (![A_27, B_28, C_29]: (~r1_xboole_0(A_27, B_28) | ~r2_hidden(C_29, B_28) | ~r2_hidden(C_29, A_27))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.89/1.26  tff(c_67, plain, (![C_30]: (~r2_hidden(C_30, '#skF_5') | ~r2_hidden(C_30, k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_32, c_63])).
% 1.89/1.26  tff(c_79, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(resolution, [status(thm)], [c_45, c_67])).
% 1.89/1.26  tff(c_85, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_79])).
% 1.89/1.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.26  
% 1.89/1.26  Inference rules
% 1.89/1.26  ----------------------
% 1.89/1.26  #Ref     : 0
% 1.89/1.26  #Sup     : 10
% 1.89/1.26  #Fact    : 0
% 1.89/1.26  #Define  : 0
% 1.89/1.26  #Split   : 0
% 1.89/1.26  #Chain   : 0
% 1.89/1.26  #Close   : 0
% 1.89/1.26  
% 1.89/1.26  Ordering : KBO
% 1.89/1.26  
% 1.89/1.26  Simplification rules
% 1.89/1.26  ----------------------
% 1.89/1.26  #Subsume      : 0
% 1.89/1.26  #Demod        : 2
% 1.89/1.26  #Tautology    : 5
% 1.89/1.26  #SimpNegUnit  : 0
% 1.89/1.26  #BackRed      : 0
% 1.89/1.26  
% 1.89/1.26  #Partial instantiations: 0
% 1.89/1.26  #Strategies tried      : 1
% 1.89/1.26  
% 1.89/1.26  Timing (in seconds)
% 1.89/1.26  ----------------------
% 1.89/1.26  Preprocessing        : 0.37
% 1.89/1.26  Parsing              : 0.19
% 1.89/1.26  CNF conversion       : 0.02
% 1.89/1.26  Main loop            : 0.11
% 1.89/1.26  Inferencing          : 0.04
% 1.89/1.26  Reduction            : 0.04
% 1.89/1.26  Demodulation         : 0.03
% 1.89/1.26  BG Simplification    : 0.02
% 1.89/1.26  Subsumption          : 0.02
% 1.89/1.26  Abstraction          : 0.01
% 1.89/1.26  MUC search           : 0.00
% 1.89/1.26  Cooper               : 0.00
% 1.89/1.26  Total                : 0.51
% 1.89/1.26  Index Insertion      : 0.00
% 1.89/1.26  Index Deletion       : 0.00
% 1.89/1.26  Index Matching       : 0.00
% 1.89/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:04 EST 2020

% Result     : Theorem 2.24s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   31 (  32 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   26 (  28 expanded)
%              Number of equality atoms :   10 (  11 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_55,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(A,k1_tarski(B)) = k1_tarski(B)
       => r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_zfmisc_1)).

tff(f_48,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_44,plain,(
    ~ r2_hidden('#skF_6','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_40,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_56,plain,(
    ! [D_19,B_20] : r2_hidden(D_19,k2_tarski(D_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_59,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_56])).

tff(c_46,plain,(
    k3_xboole_0('#skF_5',k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_20,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_98,plain,(
    ! [D_31,A_32,B_33] :
      ( r2_hidden(D_31,A_32)
      | ~ r2_hidden(D_31,k4_xboole_0(A_32,B_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_102,plain,(
    ! [D_34,A_35,B_36] :
      ( r2_hidden(D_34,A_35)
      | ~ r2_hidden(D_34,k3_xboole_0(A_35,B_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_98])).

tff(c_106,plain,(
    ! [D_37] :
      ( r2_hidden(D_37,'#skF_5')
      | ~ r2_hidden(D_37,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_102])).

tff(c_110,plain,(
    r2_hidden('#skF_6','#skF_5') ),
    inference(resolution,[status(thm)],[c_59,c_106])).

tff(c_114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_110])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n014.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 20:51:07 EST 2020
% 0.15/0.34  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.24/1.54  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.55  
% 2.24/1.55  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.24/1.55  %$ r2_hidden > k2_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.24/1.55  
% 2.24/1.55  %Foreground sorts:
% 2.24/1.55  
% 2.24/1.55  
% 2.24/1.55  %Background operators:
% 2.24/1.55  
% 2.24/1.55  
% 2.24/1.55  %Foreground operators:
% 2.24/1.55  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.24/1.55  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.24/1.55  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.24/1.55  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.24/1.55  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.24/1.55  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.24/1.55  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.24/1.55  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.24/1.55  tff('#skF_5', type, '#skF_5': $i).
% 2.24/1.55  tff('#skF_6', type, '#skF_6': $i).
% 2.24/1.55  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.24/1.55  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.24/1.55  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.24/1.55  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.24/1.55  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.24/1.55  
% 2.28/1.56  tff(f_55, negated_conjecture, ~(![A, B]: ((k3_xboole_0(A, k1_tarski(B)) = k1_tarski(B)) => r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_zfmisc_1)).
% 2.28/1.56  tff(f_48, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.28/1.56  tff(f_46, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.28/1.56  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.28/1.56  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.28/1.56  tff(c_44, plain, (~r2_hidden('#skF_6', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.28/1.56  tff(c_40, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.28/1.56  tff(c_56, plain, (![D_19, B_20]: (r2_hidden(D_19, k2_tarski(D_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.28/1.56  tff(c_59, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_56])).
% 2.28/1.56  tff(c_46, plain, (k3_xboole_0('#skF_5', k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.28/1.56  tff(c_20, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.28/1.56  tff(c_98, plain, (![D_31, A_32, B_33]: (r2_hidden(D_31, A_32) | ~r2_hidden(D_31, k4_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.28/1.56  tff(c_102, plain, (![D_34, A_35, B_36]: (r2_hidden(D_34, A_35) | ~r2_hidden(D_34, k3_xboole_0(A_35, B_36)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_98])).
% 2.28/1.56  tff(c_106, plain, (![D_37]: (r2_hidden(D_37, '#skF_5') | ~r2_hidden(D_37, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_46, c_102])).
% 2.28/1.56  tff(c_110, plain, (r2_hidden('#skF_6', '#skF_5')), inference(resolution, [status(thm)], [c_59, c_106])).
% 2.28/1.56  tff(c_114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_110])).
% 2.28/1.56  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.28/1.56  
% 2.28/1.56  Inference rules
% 2.28/1.56  ----------------------
% 2.28/1.56  #Ref     : 0
% 2.28/1.56  #Sup     : 16
% 2.28/1.56  #Fact    : 0
% 2.28/1.56  #Define  : 0
% 2.28/1.56  #Split   : 0
% 2.28/1.56  #Chain   : 0
% 2.28/1.56  #Close   : 0
% 2.28/1.56  
% 2.28/1.56  Ordering : KBO
% 2.28/1.56  
% 2.28/1.56  Simplification rules
% 2.28/1.56  ----------------------
% 2.28/1.56  #Subsume      : 0
% 2.28/1.56  #Demod        : 1
% 2.28/1.56  #Tautology    : 9
% 2.28/1.56  #SimpNegUnit  : 1
% 2.28/1.56  #BackRed      : 0
% 2.28/1.56  
% 2.28/1.56  #Partial instantiations: 0
% 2.28/1.56  #Strategies tried      : 1
% 2.28/1.56  
% 2.28/1.56  Timing (in seconds)
% 2.28/1.56  ----------------------
% 2.28/1.57  Preprocessing        : 0.47
% 2.28/1.57  Parsing              : 0.23
% 2.28/1.57  CNF conversion       : 0.04
% 2.28/1.57  Main loop            : 0.19
% 2.28/1.57  Inferencing          : 0.05
% 2.28/1.57  Reduction            : 0.06
% 2.28/1.57  Demodulation         : 0.05
% 2.28/1.57  BG Simplification    : 0.02
% 2.28/1.57  Subsumption          : 0.03
% 2.28/1.57  Abstraction          : 0.02
% 2.28/1.57  MUC search           : 0.00
% 2.28/1.57  Cooper               : 0.00
% 2.28/1.57  Total                : 0.70
% 2.28/1.57  Index Insertion      : 0.00
% 2.28/1.57  Index Deletion       : 0.00
% 2.28/1.57  Index Matching       : 0.00
% 2.28/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------

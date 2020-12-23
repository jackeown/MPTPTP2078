%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:27 EST 2020

% Result     : Theorem 2.01s
% Output     : CNFRefutation 2.01s
% Verified   : 
% Statistics : Number of formulae       :   39 (  39 expanded)
%              Number of leaves         :   26 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   30 (  30 expanded)
%              Number of equality atoms :    7 (   7 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_46,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_74,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(c_14,plain,(
    ! [A_11] : r1_xboole_0(A_11,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_196,plain,(
    ! [A_46,B_47] :
      ( ~ r2_hidden(A_46,B_47)
      | ~ r1_xboole_0(k1_tarski(A_46),B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_201,plain,(
    ! [A_46] : ~ r2_hidden(A_46,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_14,c_196])).

tff(c_46,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_61,plain,(
    ! [A_32,B_33] : r1_tarski(A_32,k2_xboole_0(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_64,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_61])).

tff(c_36,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_78,plain,(
    ! [D_36,A_37] : r2_hidden(D_36,k2_tarski(A_37,D_36)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_81,plain,(
    ! [A_20] : r2_hidden(A_20,k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_78])).

tff(c_309,plain,(
    ! [C_61,B_62,A_63] :
      ( r2_hidden(C_61,B_62)
      | ~ r2_hidden(C_61,A_63)
      | ~ r1_tarski(A_63,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_325,plain,(
    ! [A_64,B_65] :
      ( r2_hidden(A_64,B_65)
      | ~ r1_tarski(k1_tarski(A_64),B_65) ) ),
    inference(resolution,[status(thm)],[c_81,c_309])).

tff(c_336,plain,(
    r2_hidden('#skF_5',k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_64,c_325])).

tff(c_350,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_201,c_336])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n011.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 16:54:27 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.01/1.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.24  
% 2.01/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_1
% 2.01/1.24  
% 2.01/1.24  %Foreground sorts:
% 2.01/1.24  
% 2.01/1.24  
% 2.01/1.24  %Background operators:
% 2.01/1.24  
% 2.01/1.24  
% 2.01/1.24  %Foreground operators:
% 2.01/1.24  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.01/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.01/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.01/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.01/1.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.01/1.24  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.01/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.01/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.01/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.01/1.24  tff('#skF_5', type, '#skF_5': $i).
% 2.01/1.24  tff('#skF_6', type, '#skF_6': $i).
% 2.01/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.01/1.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.01/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.01/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.01/1.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.01/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.01/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.01/1.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.01/1.24  
% 2.01/1.25  tff(f_46, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.01/1.25  tff(f_68, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.01/1.25  tff(f_74, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.01/1.25  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.01/1.25  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.01/1.25  tff(f_57, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.01/1.25  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.01/1.25  tff(c_14, plain, (![A_11]: (r1_xboole_0(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.01/1.25  tff(c_196, plain, (![A_46, B_47]: (~r2_hidden(A_46, B_47) | ~r1_xboole_0(k1_tarski(A_46), B_47))), inference(cnfTransformation, [status(thm)], [f_68])).
% 2.01/1.25  tff(c_201, plain, (![A_46]: (~r2_hidden(A_46, k1_xboole_0))), inference(resolution, [status(thm)], [c_14, c_196])).
% 2.01/1.25  tff(c_46, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_74])).
% 2.01/1.25  tff(c_61, plain, (![A_32, B_33]: (r1_tarski(A_32, k2_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.01/1.25  tff(c_64, plain, (r1_tarski(k1_tarski('#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_61])).
% 2.01/1.25  tff(c_36, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.01/1.25  tff(c_78, plain, (![D_36, A_37]: (r2_hidden(D_36, k2_tarski(A_37, D_36)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.01/1.25  tff(c_81, plain, (![A_20]: (r2_hidden(A_20, k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_36, c_78])).
% 2.01/1.25  tff(c_309, plain, (![C_61, B_62, A_63]: (r2_hidden(C_61, B_62) | ~r2_hidden(C_61, A_63) | ~r1_tarski(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.01/1.25  tff(c_325, plain, (![A_64, B_65]: (r2_hidden(A_64, B_65) | ~r1_tarski(k1_tarski(A_64), B_65))), inference(resolution, [status(thm)], [c_81, c_309])).
% 2.01/1.25  tff(c_336, plain, (r2_hidden('#skF_5', k1_xboole_0)), inference(resolution, [status(thm)], [c_64, c_325])).
% 2.01/1.25  tff(c_350, plain, $false, inference(negUnitSimplification, [status(thm)], [c_201, c_336])).
% 2.01/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.01/1.25  
% 2.01/1.25  Inference rules
% 2.01/1.25  ----------------------
% 2.01/1.25  #Ref     : 0
% 2.01/1.25  #Sup     : 72
% 2.01/1.25  #Fact    : 0
% 2.01/1.25  #Define  : 0
% 2.01/1.25  #Split   : 0
% 2.01/1.25  #Chain   : 0
% 2.01/1.25  #Close   : 0
% 2.01/1.25  
% 2.01/1.25  Ordering : KBO
% 2.01/1.25  
% 2.01/1.25  Simplification rules
% 2.01/1.25  ----------------------
% 2.01/1.25  #Subsume      : 2
% 2.01/1.25  #Demod        : 22
% 2.01/1.25  #Tautology    : 49
% 2.01/1.25  #SimpNegUnit  : 1
% 2.01/1.25  #BackRed      : 0
% 2.01/1.25  
% 2.01/1.25  #Partial instantiations: 0
% 2.01/1.25  #Strategies tried      : 1
% 2.01/1.25  
% 2.01/1.25  Timing (in seconds)
% 2.01/1.25  ----------------------
% 2.01/1.25  Preprocessing        : 0.29
% 2.01/1.25  Parsing              : 0.15
% 2.01/1.25  CNF conversion       : 0.02
% 2.01/1.25  Main loop            : 0.19
% 2.01/1.25  Inferencing          : 0.07
% 2.01/1.25  Reduction            : 0.08
% 2.01/1.25  Demodulation         : 0.06
% 2.01/1.25  BG Simplification    : 0.01
% 2.01/1.25  Subsumption          : 0.03
% 2.01/1.25  Abstraction          : 0.01
% 2.01/1.25  MUC search           : 0.00
% 2.01/1.25  Cooper               : 0.00
% 2.01/1.25  Total                : 0.51
% 2.01/1.25  Index Insertion      : 0.00
% 2.01/1.25  Index Deletion       : 0.00
% 2.01/1.25  Index Matching       : 0.00
% 2.01/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

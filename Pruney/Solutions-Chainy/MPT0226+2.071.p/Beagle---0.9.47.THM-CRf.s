%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:46 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   42 (  50 expanded)
%              Number of leaves         :   24 (  30 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  60 expanded)
%              Number of equality atoms :   17 (  31 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_xboole_0
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_zfmisc_1)).

tff(f_52,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_41,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_50,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_44,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_69,plain,(
    ! [D_26,A_27] : r2_hidden(D_26,k2_tarski(A_27,D_26)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_72,plain,(
    ! [A_18] : r2_hidden(A_18,k1_tarski(A_18)) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_69])).

tff(c_30,plain,(
    ! [D_17,B_13] : r2_hidden(D_17,k2_tarski(D_17,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_24,plain,(
    ! [A_11] : k4_xboole_0(k1_xboole_0,A_11) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_118,plain,(
    ! [D_40,B_41,A_42] :
      ( ~ r2_hidden(D_40,B_41)
      | ~ r2_hidden(D_40,k4_xboole_0(A_42,B_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_128,plain,(
    ! [D_43,A_44] :
      ( ~ r2_hidden(D_43,A_44)
      | ~ r2_hidden(D_43,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_118])).

tff(c_135,plain,(
    ! [D_17] : ~ r2_hidden(D_17,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_30,c_128])).

tff(c_52,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_177,plain,(
    ! [D_56,A_57,B_58] :
      ( r2_hidden(D_56,k4_xboole_0(A_57,B_58))
      | r2_hidden(D_56,B_58)
      | ~ r2_hidden(D_56,A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_189,plain,(
    ! [D_56] :
      ( r2_hidden(D_56,k1_xboole_0)
      | r2_hidden(D_56,k1_tarski('#skF_6'))
      | ~ r2_hidden(D_56,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_177])).

tff(c_210,plain,(
    ! [D_65] :
      ( r2_hidden(D_65,k1_tarski('#skF_6'))
      | ~ r2_hidden(D_65,k1_tarski('#skF_5')) ) ),
    inference(negUnitSimplification,[status(thm)],[c_135,c_189])).

tff(c_215,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_72,c_210])).

tff(c_148,plain,(
    ! [D_48,B_49,A_50] :
      ( D_48 = B_49
      | D_48 = A_50
      | ~ r2_hidden(D_48,k2_tarski(A_50,B_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_157,plain,(
    ! [D_48,A_18] :
      ( D_48 = A_18
      | D_48 = A_18
      | ~ r2_hidden(D_48,k1_tarski(A_18)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_148])).

tff(c_218,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_215,c_157])).

tff(c_222,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_218])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:20:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.42  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.43  
% 1.92/1.43  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.43  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.92/1.43  
% 1.92/1.43  %Foreground sorts:
% 1.92/1.43  
% 1.92/1.43  
% 1.92/1.43  %Background operators:
% 1.92/1.43  
% 1.92/1.43  
% 1.92/1.43  %Foreground operators:
% 1.92/1.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.92/1.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.92/1.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.92/1.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.43  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.92/1.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.92/1.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.92/1.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.43  tff('#skF_5', type, '#skF_5': $i).
% 1.92/1.43  tff('#skF_6', type, '#skF_6': $i).
% 1.92/1.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.92/1.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.92/1.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.43  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.92/1.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.92/1.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.92/1.43  
% 1.92/1.45  tff(f_61, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_xboole_0) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_zfmisc_1)).
% 1.92/1.45  tff(f_52, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.92/1.45  tff(f_50, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.92/1.45  tff(f_41, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.92/1.45  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 1.92/1.45  tff(c_50, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.45  tff(c_44, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.92/1.45  tff(c_69, plain, (![D_26, A_27]: (r2_hidden(D_26, k2_tarski(A_27, D_26)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.92/1.45  tff(c_72, plain, (![A_18]: (r2_hidden(A_18, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_69])).
% 1.92/1.45  tff(c_30, plain, (![D_17, B_13]: (r2_hidden(D_17, k2_tarski(D_17, B_13)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.92/1.45  tff(c_24, plain, (![A_11]: (k4_xboole_0(k1_xboole_0, A_11)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.92/1.45  tff(c_118, plain, (![D_40, B_41, A_42]: (~r2_hidden(D_40, B_41) | ~r2_hidden(D_40, k4_xboole_0(A_42, B_41)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.45  tff(c_128, plain, (![D_43, A_44]: (~r2_hidden(D_43, A_44) | ~r2_hidden(D_43, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_24, c_118])).
% 1.92/1.45  tff(c_135, plain, (![D_17]: (~r2_hidden(D_17, k1_xboole_0))), inference(resolution, [status(thm)], [c_30, c_128])).
% 1.92/1.45  tff(c_52, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.92/1.45  tff(c_177, plain, (![D_56, A_57, B_58]: (r2_hidden(D_56, k4_xboole_0(A_57, B_58)) | r2_hidden(D_56, B_58) | ~r2_hidden(D_56, A_57))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.92/1.45  tff(c_189, plain, (![D_56]: (r2_hidden(D_56, k1_xboole_0) | r2_hidden(D_56, k1_tarski('#skF_6')) | ~r2_hidden(D_56, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_177])).
% 1.92/1.45  tff(c_210, plain, (![D_65]: (r2_hidden(D_65, k1_tarski('#skF_6')) | ~r2_hidden(D_65, k1_tarski('#skF_5')))), inference(negUnitSimplification, [status(thm)], [c_135, c_189])).
% 1.92/1.45  tff(c_215, plain, (r2_hidden('#skF_5', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_72, c_210])).
% 1.92/1.45  tff(c_148, plain, (![D_48, B_49, A_50]: (D_48=B_49 | D_48=A_50 | ~r2_hidden(D_48, k2_tarski(A_50, B_49)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.92/1.45  tff(c_157, plain, (![D_48, A_18]: (D_48=A_18 | D_48=A_18 | ~r2_hidden(D_48, k1_tarski(A_18)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_148])).
% 1.92/1.45  tff(c_218, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_215, c_157])).
% 1.92/1.45  tff(c_222, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_50, c_218])).
% 1.92/1.45  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.45  
% 1.92/1.45  Inference rules
% 1.92/1.45  ----------------------
% 1.92/1.45  #Ref     : 0
% 1.92/1.45  #Sup     : 40
% 1.92/1.45  #Fact    : 0
% 1.92/1.45  #Define  : 0
% 1.92/1.45  #Split   : 0
% 1.92/1.45  #Chain   : 0
% 1.92/1.45  #Close   : 0
% 1.92/1.45  
% 1.92/1.45  Ordering : KBO
% 1.92/1.45  
% 1.92/1.45  Simplification rules
% 1.92/1.45  ----------------------
% 1.92/1.45  #Subsume      : 8
% 1.92/1.45  #Demod        : 1
% 1.92/1.45  #Tautology    : 23
% 1.92/1.45  #SimpNegUnit  : 4
% 1.92/1.45  #BackRed      : 0
% 1.92/1.45  
% 1.92/1.45  #Partial instantiations: 0
% 1.92/1.45  #Strategies tried      : 1
% 1.92/1.45  
% 1.92/1.45  Timing (in seconds)
% 1.92/1.45  ----------------------
% 1.92/1.45  Preprocessing        : 0.39
% 1.92/1.45  Parsing              : 0.18
% 1.92/1.45  CNF conversion       : 0.03
% 1.92/1.45  Main loop            : 0.20
% 1.92/1.45  Inferencing          : 0.07
% 1.92/1.45  Reduction            : 0.07
% 1.92/1.45  Demodulation         : 0.05
% 1.92/1.45  BG Simplification    : 0.02
% 1.92/1.45  Subsumption          : 0.04
% 1.92/1.45  Abstraction          : 0.01
% 1.92/1.45  MUC search           : 0.00
% 1.92/1.45  Cooper               : 0.00
% 1.92/1.45  Total                : 0.63
% 1.92/1.45  Index Insertion      : 0.00
% 1.92/1.45  Index Deletion       : 0.00
% 1.92/1.46  Index Matching       : 0.00
% 1.92/1.46  BG Taut test         : 0.00
%------------------------------------------------------------------------------

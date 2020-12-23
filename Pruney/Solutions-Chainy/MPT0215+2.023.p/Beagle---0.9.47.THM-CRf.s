%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:41 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.62s
% Verified   : 
% Statistics : Number of formulae       :   23 (  24 expanded)
%              Number of leaves         :   16 (  17 expanded)
%              Depth                    :    4
%              Number of atoms          :   17 (  19 expanded)
%              Number of equality atoms :   11 (  13 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_32,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    k2_tarski('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_40,plain,(
    ! [D_13,B_14] : r2_hidden(D_13,k2_tarski(D_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_43,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_40])).

tff(c_48,plain,(
    ! [C_17,A_18] :
      ( C_17 = A_18
      | ~ r2_hidden(C_17,k1_tarski(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_54,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_43,c_48])).

tff(c_62,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_54])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n025.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 11:58:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.09  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.10  
% 1.62/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.10  %$ r2_hidden > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 1.62/1.10  
% 1.62/1.10  %Foreground sorts:
% 1.62/1.10  
% 1.62/1.10  
% 1.62/1.10  %Background operators:
% 1.62/1.10  
% 1.62/1.10  
% 1.62/1.10  %Foreground operators:
% 1.62/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.10  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.62/1.10  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.62/1.10  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.62/1.10  tff('#skF_7', type, '#skF_7': $i).
% 1.62/1.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.62/1.10  tff('#skF_5', type, '#skF_5': $i).
% 1.62/1.10  tff('#skF_6', type, '#skF_6': $i).
% 1.62/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.10  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.62/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.10  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.62/1.10  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.62/1.10  
% 1.62/1.10  tff(f_46, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_zfmisc_1)).
% 1.62/1.10  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.62/1.10  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.62/1.10  tff(c_32, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.62/1.10  tff(c_34, plain, (k2_tarski('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.62/1.10  tff(c_40, plain, (![D_13, B_14]: (r2_hidden(D_13, k2_tarski(D_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.62/1.10  tff(c_43, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_40])).
% 1.62/1.10  tff(c_48, plain, (![C_17, A_18]: (C_17=A_18 | ~r2_hidden(C_17, k1_tarski(A_18)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.62/1.10  tff(c_54, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_43, c_48])).
% 1.62/1.10  tff(c_62, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_54])).
% 1.62/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.10  
% 1.62/1.10  Inference rules
% 1.62/1.10  ----------------------
% 1.62/1.10  #Ref     : 0
% 1.62/1.10  #Sup     : 7
% 1.62/1.10  #Fact    : 0
% 1.62/1.10  #Define  : 0
% 1.62/1.10  #Split   : 0
% 1.62/1.10  #Chain   : 0
% 1.62/1.10  #Close   : 0
% 1.62/1.10  
% 1.62/1.10  Ordering : KBO
% 1.62/1.10  
% 1.62/1.10  Simplification rules
% 1.62/1.10  ----------------------
% 1.62/1.10  #Subsume      : 0
% 1.62/1.10  #Demod        : 0
% 1.62/1.10  #Tautology    : 2
% 1.62/1.10  #SimpNegUnit  : 1
% 1.62/1.10  #BackRed      : 0
% 1.62/1.10  
% 1.62/1.10  #Partial instantiations: 0
% 1.62/1.10  #Strategies tried      : 1
% 1.62/1.11  
% 1.62/1.11  Timing (in seconds)
% 1.62/1.11  ----------------------
% 1.62/1.11  Preprocessing        : 0.28
% 1.62/1.11  Parsing              : 0.14
% 1.62/1.11  CNF conversion       : 0.02
% 1.62/1.11  Main loop            : 0.08
% 1.62/1.11  Inferencing          : 0.02
% 1.62/1.11  Reduction            : 0.02
% 1.62/1.11  Demodulation         : 0.01
% 1.62/1.11  BG Simplification    : 0.01
% 1.62/1.11  Subsumption          : 0.02
% 1.62/1.11  Abstraction          : 0.01
% 1.62/1.11  MUC search           : 0.00
% 1.62/1.11  Cooper               : 0.00
% 1.62/1.11  Total                : 0.38
% 1.62/1.11  Index Insertion      : 0.00
% 1.62/1.11  Index Deletion       : 0.00
% 1.62/1.11  Index Matching       : 0.00
% 1.62/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------

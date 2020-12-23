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
% DateTime   : Thu Dec  3 09:47:44 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   27 (  33 expanded)
%              Number of leaves         :   16 (  20 expanded)
%              Depth                    :    5
%              Number of atoms          :   21 (  35 expanded)
%              Number of equality atoms :   13 (  24 expanded)
%              Maximal formula depth    :    8 (   3 average)
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
       => B = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

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

tff(c_34,plain,(
    k2_tarski('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_44,plain,(
    ! [D_15,A_16] : r2_hidden(D_15,k2_tarski(A_16,D_15)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_47,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_44])).

tff(c_48,plain,(
    ! [C_17,A_18] :
      ( C_17 = A_18
      | ~ r2_hidden(C_17,k1_tarski(A_18)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_58,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_47,c_48])).

tff(c_32,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_32])).

tff(c_40,plain,(
    ! [D_13,B_14] : r2_hidden(D_13,k2_tarski(D_13,B_14)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_43,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_34,c_40])).

tff(c_59,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_43,c_48])).

tff(c_70,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_59])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:42:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.10  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.10  
% 1.61/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.11  %$ r2_hidden > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_1
% 1.61/1.11  
% 1.61/1.11  %Foreground sorts:
% 1.61/1.11  
% 1.61/1.11  
% 1.61/1.11  %Background operators:
% 1.61/1.11  
% 1.61/1.11  
% 1.61/1.11  %Foreground operators:
% 1.61/1.11  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.11  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.61/1.11  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.61/1.11  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.61/1.11  tff('#skF_7', type, '#skF_7': $i).
% 1.61/1.11  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.61/1.11  tff('#skF_5', type, '#skF_5': $i).
% 1.61/1.11  tff('#skF_6', type, '#skF_6': $i).
% 1.61/1.11  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.11  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.61/1.11  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.11  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.61/1.11  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.61/1.11  
% 1.61/1.11  tff(f_46, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (B = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 1.61/1.11  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.61/1.11  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.61/1.11  tff(c_34, plain, (k2_tarski('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.61/1.11  tff(c_44, plain, (![D_15, A_16]: (r2_hidden(D_15, k2_tarski(A_16, D_15)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.61/1.11  tff(c_47, plain, (r2_hidden('#skF_7', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_44])).
% 1.61/1.11  tff(c_48, plain, (![C_17, A_18]: (C_17=A_18 | ~r2_hidden(C_17, k1_tarski(A_18)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.61/1.11  tff(c_58, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_47, c_48])).
% 1.61/1.11  tff(c_32, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.61/1.11  tff(c_64, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_58, c_32])).
% 1.61/1.11  tff(c_40, plain, (![D_13, B_14]: (r2_hidden(D_13, k2_tarski(D_13, B_14)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.61/1.11  tff(c_43, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_34, c_40])).
% 1.61/1.11  tff(c_59, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_43, c_48])).
% 1.61/1.11  tff(c_70, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_59])).
% 1.61/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.11  
% 1.61/1.11  Inference rules
% 1.61/1.11  ----------------------
% 1.61/1.11  #Ref     : 0
% 1.61/1.11  #Sup     : 9
% 1.61/1.11  #Fact    : 0
% 1.61/1.11  #Define  : 0
% 1.61/1.11  #Split   : 0
% 1.61/1.11  #Chain   : 0
% 1.61/1.11  #Close   : 0
% 1.61/1.11  
% 1.61/1.11  Ordering : KBO
% 1.61/1.11  
% 1.61/1.11  Simplification rules
% 1.61/1.11  ----------------------
% 1.61/1.11  #Subsume      : 0
% 1.61/1.11  #Demod        : 4
% 1.61/1.11  #Tautology    : 6
% 1.61/1.11  #SimpNegUnit  : 1
% 1.61/1.11  #BackRed      : 3
% 1.61/1.11  
% 1.61/1.11  #Partial instantiations: 0
% 1.61/1.11  #Strategies tried      : 1
% 1.61/1.11  
% 1.61/1.11  Timing (in seconds)
% 1.61/1.11  ----------------------
% 1.61/1.12  Preprocessing        : 0.27
% 1.61/1.12  Parsing              : 0.13
% 1.61/1.12  CNF conversion       : 0.02
% 1.68/1.12  Main loop            : 0.09
% 1.68/1.12  Inferencing          : 0.02
% 1.68/1.12  Reduction            : 0.03
% 1.68/1.12  Demodulation         : 0.02
% 1.68/1.12  BG Simplification    : 0.01
% 1.68/1.12  Subsumption          : 0.02
% 1.68/1.12  Abstraction          : 0.01
% 1.68/1.12  MUC search           : 0.00
% 1.68/1.12  Cooper               : 0.00
% 1.68/1.12  Total                : 0.38
% 1.68/1.12  Index Insertion      : 0.00
% 1.68/1.12  Index Deletion       : 0.00
% 1.68/1.12  Index Matching       : 0.00
% 1.68/1.12  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 10:08:59 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   37 (  52 expanded)
%              Number of leaves         :   20 (  28 expanded)
%              Depth                    :    4
%              Number of atoms          :   41 (  83 expanded)
%              Number of equality atoms :   20 (  39 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_42,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_36,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_42,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_34,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),'#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_77,plain,(
    ! [A_37,C_38,B_39] :
      ( r2_hidden(k2_mcart_1(A_37),C_38)
      | ~ r2_hidden(A_37,k2_zfmisc_1(B_39,C_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_79,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(resolution,[status(thm)],[c_34,c_77])).

tff(c_83,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_79])).

tff(c_85,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_38,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | ~ r2_hidden(k2_mcart_1('#skF_3'),'#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_108,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_85,c_38])).

tff(c_84,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_109,plain,(
    ! [A_46,B_47,C_48] :
      ( r2_hidden(k1_mcart_1(A_46),B_47)
      | ~ r2_hidden(A_46,k2_zfmisc_1(B_47,C_48)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_112,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_109])).

tff(c_26,plain,(
    ! [A_8,B_9] : k1_enumset1(A_8,A_8,B_9) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_127,plain,(
    ! [E_55,C_56,B_57,A_58] :
      ( E_55 = C_56
      | E_55 = B_57
      | E_55 = A_58
      | ~ r2_hidden(E_55,k1_enumset1(A_58,B_57,C_56)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_146,plain,(
    ! [E_59,B_60,A_61] :
      ( E_59 = B_60
      | E_59 = A_61
      | E_59 = A_61
      | ~ r2_hidden(E_59,k2_tarski(A_61,B_60)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_127])).

tff(c_149,plain,
    ( k1_mcart_1('#skF_3') = '#skF_5'
    | k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_112,c_146])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_108,c_108,c_84,c_149])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:21:06 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.80/1.18  
% 1.80/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.18  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 1.91/1.18  
% 1.91/1.18  %Foreground sorts:
% 1.91/1.18  
% 1.91/1.18  
% 1.91/1.18  %Background operators:
% 1.91/1.18  
% 1.91/1.18  
% 1.91/1.18  %Foreground operators:
% 1.91/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.91/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.91/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.91/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.91/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.91/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.91/1.18  tff('#skF_6', type, '#skF_6': $i).
% 1.91/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.91/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.91/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.91/1.18  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.91/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.91/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.91/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.91/1.18  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.91/1.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 1.91/1.18  
% 1.91/1.19  tff(f_59, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_mcart_1)).
% 1.91/1.19  tff(f_50, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.91/1.19  tff(f_42, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 1.91/1.19  tff(f_40, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 1.91/1.19  tff(c_36, plain, (k1_mcart_1('#skF_3')!='#skF_5' | ~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.91/1.19  tff(c_42, plain, (~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(splitLeft, [status(thm)], [c_36])).
% 1.91/1.19  tff(c_34, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.91/1.19  tff(c_77, plain, (![A_37, C_38, B_39]: (r2_hidden(k2_mcart_1(A_37), C_38) | ~r2_hidden(A_37, k2_zfmisc_1(B_39, C_38)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.91/1.19  tff(c_79, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(resolution, [status(thm)], [c_34, c_77])).
% 1.91/1.19  tff(c_83, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_79])).
% 1.91/1.19  tff(c_85, plain, (r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(splitRight, [status(thm)], [c_36])).
% 1.91/1.19  tff(c_38, plain, (k1_mcart_1('#skF_3')!='#skF_4' | ~r2_hidden(k2_mcart_1('#skF_3'), '#skF_6')), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.91/1.19  tff(c_108, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_85, c_38])).
% 1.91/1.19  tff(c_84, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_36])).
% 1.91/1.19  tff(c_109, plain, (![A_46, B_47, C_48]: (r2_hidden(k1_mcart_1(A_46), B_47) | ~r2_hidden(A_46, k2_zfmisc_1(B_47, C_48)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.91/1.19  tff(c_112, plain, (r2_hidden(k1_mcart_1('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_34, c_109])).
% 1.91/1.19  tff(c_26, plain, (![A_8, B_9]: (k1_enumset1(A_8, A_8, B_9)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.91/1.19  tff(c_127, plain, (![E_55, C_56, B_57, A_58]: (E_55=C_56 | E_55=B_57 | E_55=A_58 | ~r2_hidden(E_55, k1_enumset1(A_58, B_57, C_56)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.91/1.19  tff(c_146, plain, (![E_59, B_60, A_61]: (E_59=B_60 | E_59=A_61 | E_59=A_61 | ~r2_hidden(E_59, k2_tarski(A_61, B_60)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_127])).
% 1.91/1.19  tff(c_149, plain, (k1_mcart_1('#skF_3')='#skF_5' | k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_112, c_146])).
% 1.91/1.19  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_108, c_108, c_84, c_149])).
% 1.91/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.91/1.19  
% 1.91/1.19  Inference rules
% 1.91/1.19  ----------------------
% 1.91/1.19  #Ref     : 0
% 1.91/1.19  #Sup     : 25
% 1.91/1.19  #Fact    : 0
% 1.91/1.19  #Define  : 0
% 1.91/1.19  #Split   : 1
% 1.91/1.19  #Chain   : 0
% 1.91/1.19  #Close   : 0
% 1.91/1.19  
% 1.91/1.19  Ordering : KBO
% 1.91/1.19  
% 1.91/1.19  Simplification rules
% 1.91/1.19  ----------------------
% 1.91/1.19  #Subsume      : 1
% 1.91/1.19  #Demod        : 4
% 1.91/1.19  #Tautology    : 14
% 1.91/1.19  #SimpNegUnit  : 2
% 1.91/1.19  #BackRed      : 0
% 1.91/1.19  
% 1.91/1.19  #Partial instantiations: 0
% 1.91/1.19  #Strategies tried      : 1
% 1.91/1.19  
% 1.91/1.19  Timing (in seconds)
% 1.91/1.19  ----------------------
% 1.91/1.19  Preprocessing        : 0.29
% 1.91/1.19  Parsing              : 0.14
% 1.91/1.19  CNF conversion       : 0.02
% 1.91/1.19  Main loop            : 0.14
% 1.91/1.19  Inferencing          : 0.05
% 1.91/1.19  Reduction            : 0.04
% 1.91/1.19  Demodulation         : 0.03
% 1.91/1.19  BG Simplification    : 0.01
% 1.91/1.19  Subsumption          : 0.02
% 1.91/1.19  Abstraction          : 0.01
% 1.91/1.19  MUC search           : 0.00
% 1.91/1.19  Cooper               : 0.00
% 1.91/1.19  Total                : 0.45
% 1.91/1.19  Index Insertion      : 0.00
% 1.91/1.19  Index Deletion       : 0.00
% 1.91/1.19  Index Matching       : 0.00
% 1.91/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

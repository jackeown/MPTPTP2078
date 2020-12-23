%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:05 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   39 (  48 expanded)
%              Number of leaves         :   22 (  28 expanded)
%              Depth                    :    4
%              Number of atoms          :   39 (  67 expanded)
%              Number of equality atoms :   22 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k2_tarski(C,D)))
       => ( k1_mcart_1(A) = B
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_mcart_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_42,plain,
    ( k2_mcart_1('#skF_5') != '#skF_8'
    | k1_mcart_1('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_65,plain,(
    k1_mcart_1('#skF_5') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_40,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k1_tarski('#skF_6'),k2_tarski('#skF_7','#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_85,plain,(
    ! [A_31,B_32,C_33] :
      ( r2_hidden(k1_mcart_1(A_31),B_32)
      | ~ r2_hidden(A_31,k2_zfmisc_1(B_32,C_33)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_88,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_40,c_85])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_91,plain,(
    k1_mcart_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_88,c_2])).

tff(c_95,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_91])).

tff(c_97,plain,(
    k1_mcart_1('#skF_5') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_44,plain,
    ( k2_mcart_1('#skF_5') != '#skF_7'
    | k1_mcart_1('#skF_5') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_103,plain,(
    k2_mcart_1('#skF_5') != '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_97,c_44])).

tff(c_96,plain,(
    k2_mcart_1('#skF_5') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_119,plain,(
    ! [A_38,C_39,B_40] :
      ( r2_hidden(k2_mcart_1(A_38),C_39)
      | ~ r2_hidden(A_38,k2_zfmisc_1(B_40,C_39)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_122,plain,(
    r2_hidden(k2_mcart_1('#skF_5'),k2_tarski('#skF_7','#skF_8')) ),
    inference(resolution,[status(thm)],[c_40,c_119])).

tff(c_123,plain,(
    ! [D_41,B_42,A_43] :
      ( D_41 = B_42
      | D_41 = A_43
      | ~ r2_hidden(D_41,k2_tarski(A_43,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_126,plain,
    ( k2_mcart_1('#skF_5') = '#skF_8'
    | k2_mcart_1('#skF_5') = '#skF_7' ),
    inference(resolution,[status(thm)],[c_122,c_123])).

tff(c_139,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_96,c_126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.10  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.00/0.10  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.10/0.31  % Computer   : n015.cluster.edu
% 0.10/0.31  % Model      : x86_64 x86_64
% 0.10/0.31  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.10/0.31  % Memory     : 8042.1875MB
% 0.10/0.31  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.10/0.31  % CPULimit   : 60
% 0.10/0.31  % DateTime   : Tue Dec  1 10:22:38 EST 2020
% 0.10/0.31  % CPUTime    : 
% 0.16/0.31  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.20  
% 2.07/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.20  %$ r2_hidden > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 2.07/1.20  
% 2.07/1.20  %Foreground sorts:
% 2.07/1.20  
% 2.07/1.20  
% 2.07/1.20  %Background operators:
% 2.07/1.20  
% 2.07/1.20  
% 2.07/1.20  %Foreground operators:
% 2.07/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.20  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.07/1.20  tff('#skF_7', type, '#skF_7': $i).
% 2.07/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.20  tff('#skF_5', type, '#skF_5': $i).
% 2.07/1.20  tff('#skF_6', type, '#skF_6': $i).
% 2.07/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.20  tff('#skF_8', type, '#skF_8': $i).
% 2.07/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.20  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.07/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.07/1.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.07/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.07/1.20  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.07/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.07/1.20  
% 2.07/1.21  tff(f_60, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k2_tarski(C, D))) => ((k1_mcart_1(A) = B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_mcart_1)).
% 2.07/1.21  tff(f_51, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 2.07/1.21  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.07/1.21  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.07/1.21  tff(c_42, plain, (k2_mcart_1('#skF_5')!='#skF_8' | k1_mcart_1('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.21  tff(c_65, plain, (k1_mcart_1('#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_42])).
% 2.07/1.21  tff(c_40, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k1_tarski('#skF_6'), k2_tarski('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.21  tff(c_85, plain, (![A_31, B_32, C_33]: (r2_hidden(k1_mcart_1(A_31), B_32) | ~r2_hidden(A_31, k2_zfmisc_1(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.07/1.21  tff(c_88, plain, (r2_hidden(k1_mcart_1('#skF_5'), k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_85])).
% 2.07/1.21  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.07/1.21  tff(c_91, plain, (k1_mcart_1('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_88, c_2])).
% 2.07/1.21  tff(c_95, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_91])).
% 2.07/1.21  tff(c_97, plain, (k1_mcart_1('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_42])).
% 2.07/1.21  tff(c_44, plain, (k2_mcart_1('#skF_5')!='#skF_7' | k1_mcart_1('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.07/1.21  tff(c_103, plain, (k2_mcart_1('#skF_5')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_44])).
% 2.07/1.21  tff(c_96, plain, (k2_mcart_1('#skF_5')!='#skF_8'), inference(splitRight, [status(thm)], [c_42])).
% 2.07/1.21  tff(c_119, plain, (![A_38, C_39, B_40]: (r2_hidden(k2_mcart_1(A_38), C_39) | ~r2_hidden(A_38, k2_zfmisc_1(B_40, C_39)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.07/1.21  tff(c_122, plain, (r2_hidden(k2_mcart_1('#skF_5'), k2_tarski('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_40, c_119])).
% 2.07/1.21  tff(c_123, plain, (![D_41, B_42, A_43]: (D_41=B_42 | D_41=A_43 | ~r2_hidden(D_41, k2_tarski(A_43, B_42)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.07/1.21  tff(c_126, plain, (k2_mcart_1('#skF_5')='#skF_8' | k2_mcart_1('#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_122, c_123])).
% 2.07/1.21  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_96, c_126])).
% 2.07/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.07/1.21  
% 2.07/1.21  Inference rules
% 2.07/1.21  ----------------------
% 2.07/1.21  #Ref     : 0
% 2.07/1.21  #Sup     : 20
% 2.07/1.21  #Fact    : 0
% 2.07/1.21  #Define  : 0
% 2.07/1.21  #Split   : 1
% 2.07/1.21  #Chain   : 0
% 2.07/1.21  #Close   : 0
% 2.07/1.21  
% 2.07/1.21  Ordering : KBO
% 2.07/1.21  
% 2.07/1.21  Simplification rules
% 2.07/1.21  ----------------------
% 2.07/1.21  #Subsume      : 1
% 2.07/1.21  #Demod        : 3
% 2.07/1.21  #Tautology    : 12
% 2.07/1.21  #SimpNegUnit  : 2
% 2.07/1.21  #BackRed      : 0
% 2.07/1.21  
% 2.07/1.21  #Partial instantiations: 0
% 2.07/1.21  #Strategies tried      : 1
% 2.07/1.21  
% 2.07/1.21  Timing (in seconds)
% 2.07/1.21  ----------------------
% 2.07/1.22  Preprocessing        : 0.33
% 2.07/1.22  Parsing              : 0.17
% 2.07/1.22  CNF conversion       : 0.03
% 2.07/1.22  Main loop            : 0.14
% 2.07/1.22  Inferencing          : 0.04
% 2.07/1.22  Reduction            : 0.05
% 2.07/1.22  Demodulation         : 0.04
% 2.07/1.22  BG Simplification    : 0.01
% 2.07/1.22  Subsumption          : 0.02
% 2.07/1.22  Abstraction          : 0.01
% 2.07/1.22  MUC search           : 0.00
% 2.07/1.22  Cooper               : 0.00
% 2.07/1.22  Total                : 0.49
% 2.07/1.22  Index Insertion      : 0.00
% 2.07/1.22  Index Deletion       : 0.00
% 2.07/1.22  Index Matching       : 0.00
% 2.07/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------

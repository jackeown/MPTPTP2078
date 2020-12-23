%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:05 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.88s
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
%$ r2_hidden > k2_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:19:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.16  
% 1.70/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.70/1.16  %$ r2_hidden > k2_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 1.70/1.16  
% 1.70/1.16  %Foreground sorts:
% 1.70/1.16  
% 1.70/1.16  
% 1.70/1.16  %Background operators:
% 1.70/1.16  
% 1.70/1.16  
% 1.70/1.16  %Foreground operators:
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.70/1.16  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.70/1.16  tff('#skF_7', type, '#skF_7': $i).
% 1.70/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.70/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.70/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.70/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.70/1.16  tff('#skF_8', type, '#skF_8': $i).
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.16  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.70/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.70/1.16  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.70/1.16  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.70/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.70/1.16  
% 1.88/1.17  tff(f_60, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k2_tarski(C, D))) => ((k1_mcart_1(A) = B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_mcart_1)).
% 1.88/1.17  tff(f_51, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.88/1.17  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.88/1.17  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.88/1.17  tff(c_42, plain, (k2_mcart_1('#skF_5')!='#skF_8' | k1_mcart_1('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.88/1.17  tff(c_65, plain, (k1_mcart_1('#skF_5')!='#skF_6'), inference(splitLeft, [status(thm)], [c_42])).
% 1.88/1.17  tff(c_40, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k1_tarski('#skF_6'), k2_tarski('#skF_7', '#skF_8')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.88/1.17  tff(c_85, plain, (![A_31, B_32, C_33]: (r2_hidden(k1_mcart_1(A_31), B_32) | ~r2_hidden(A_31, k2_zfmisc_1(B_32, C_33)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.17  tff(c_88, plain, (r2_hidden(k1_mcart_1('#skF_5'), k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_40, c_85])).
% 1.88/1.17  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.88/1.17  tff(c_91, plain, (k1_mcart_1('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_88, c_2])).
% 1.88/1.17  tff(c_95, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_91])).
% 1.88/1.17  tff(c_97, plain, (k1_mcart_1('#skF_5')='#skF_6'), inference(splitRight, [status(thm)], [c_42])).
% 1.88/1.17  tff(c_44, plain, (k2_mcart_1('#skF_5')!='#skF_7' | k1_mcart_1('#skF_5')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.88/1.17  tff(c_103, plain, (k2_mcart_1('#skF_5')!='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_97, c_44])).
% 1.88/1.17  tff(c_96, plain, (k2_mcart_1('#skF_5')!='#skF_8'), inference(splitRight, [status(thm)], [c_42])).
% 1.88/1.17  tff(c_119, plain, (![A_38, C_39, B_40]: (r2_hidden(k2_mcart_1(A_38), C_39) | ~r2_hidden(A_38, k2_zfmisc_1(B_40, C_39)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.88/1.17  tff(c_122, plain, (r2_hidden(k2_mcart_1('#skF_5'), k2_tarski('#skF_7', '#skF_8'))), inference(resolution, [status(thm)], [c_40, c_119])).
% 1.88/1.17  tff(c_123, plain, (![D_41, B_42, A_43]: (D_41=B_42 | D_41=A_43 | ~r2_hidden(D_41, k2_tarski(A_43, B_42)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.88/1.17  tff(c_126, plain, (k2_mcart_1('#skF_5')='#skF_8' | k2_mcart_1('#skF_5')='#skF_7'), inference(resolution, [status(thm)], [c_122, c_123])).
% 1.88/1.17  tff(c_139, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_96, c_126])).
% 1.88/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.88/1.17  
% 1.88/1.17  Inference rules
% 1.88/1.17  ----------------------
% 1.88/1.17  #Ref     : 0
% 1.88/1.17  #Sup     : 20
% 1.88/1.17  #Fact    : 0
% 1.88/1.17  #Define  : 0
% 1.88/1.17  #Split   : 1
% 1.88/1.17  #Chain   : 0
% 1.88/1.17  #Close   : 0
% 1.88/1.17  
% 1.88/1.17  Ordering : KBO
% 1.88/1.17  
% 1.88/1.17  Simplification rules
% 1.88/1.17  ----------------------
% 1.88/1.17  #Subsume      : 1
% 1.88/1.17  #Demod        : 3
% 1.88/1.17  #Tautology    : 12
% 1.88/1.17  #SimpNegUnit  : 2
% 1.88/1.17  #BackRed      : 0
% 1.88/1.17  
% 1.88/1.17  #Partial instantiations: 0
% 1.88/1.17  #Strategies tried      : 1
% 1.88/1.17  
% 1.88/1.17  Timing (in seconds)
% 1.88/1.17  ----------------------
% 1.88/1.17  Preprocessing        : 0.30
% 1.88/1.17  Parsing              : 0.15
% 1.88/1.17  CNF conversion       : 0.02
% 1.88/1.17  Main loop            : 0.12
% 1.88/1.17  Inferencing          : 0.04
% 1.88/1.17  Reduction            : 0.04
% 1.88/1.17  Demodulation         : 0.03
% 1.88/1.17  BG Simplification    : 0.01
% 1.88/1.17  Subsumption          : 0.02
% 1.88/1.17  Abstraction          : 0.01
% 1.88/1.17  MUC search           : 0.00
% 1.88/1.17  Cooper               : 0.00
% 1.88/1.17  Total                : 0.44
% 1.88/1.17  Index Insertion      : 0.00
% 1.88/1.17  Index Deletion       : 0.00
% 1.88/1.17  Index Matching       : 0.00
% 1.88/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------

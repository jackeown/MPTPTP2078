%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:02 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
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
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_42,plain,
    ( k1_mcart_1('#skF_5') != '#skF_7'
    | k2_mcart_1('#skF_5') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_65,plain,(
    k2_mcart_1('#skF_5') != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_40,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_81,plain,(
    ! [A_28,C_29,B_30] :
      ( r2_hidden(k2_mcart_1(A_28),C_29)
      | ~ r2_hidden(A_28,k2_zfmisc_1(B_30,C_29)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_84,plain,(
    r2_hidden(k2_mcart_1('#skF_5'),k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_40,c_81])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_87,plain,(
    k2_mcart_1('#skF_5') = '#skF_8' ),
    inference(resolution,[status(thm)],[c_84,c_2])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_87])).

tff(c_93,plain,(
    k2_mcart_1('#skF_5') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_44,plain,
    ( k1_mcart_1('#skF_5') != '#skF_6'
    | k2_mcart_1('#skF_5') != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_105,plain,(
    k1_mcart_1('#skF_5') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_44])).

tff(c_92,plain,(
    k1_mcart_1('#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_115,plain,(
    ! [A_35,B_36,C_37] :
      ( r2_hidden(k1_mcart_1(A_35),B_36)
      | ~ r2_hidden(A_35,k2_zfmisc_1(B_36,C_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_118,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_40,c_115])).

tff(c_124,plain,(
    ! [D_41,B_42,A_43] :
      ( D_41 = B_42
      | D_41 = A_43
      | ~ r2_hidden(D_41,k2_tarski(A_43,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_127,plain,
    ( k1_mcart_1('#skF_5') = '#skF_7'
    | k1_mcart_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_118,c_124])).

tff(c_140,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_105,c_92,c_127])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n012.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:27:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.21  
% 1.86/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.21  %$ r2_hidden > k2_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_8 > #skF_3 > #skF_2 > #skF_1
% 1.86/1.21  
% 1.86/1.21  %Foreground sorts:
% 1.86/1.21  
% 1.86/1.21  
% 1.86/1.21  %Background operators:
% 1.86/1.21  
% 1.86/1.21  
% 1.86/1.21  %Foreground operators:
% 1.86/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.86/1.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.86/1.21  tff('#skF_7', type, '#skF_7': $i).
% 1.86/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.86/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.86/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.86/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.86/1.21  tff('#skF_8', type, '#skF_8': $i).
% 1.86/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.21  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.86/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.86/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.86/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.21  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.86/1.21  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.86/1.21  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.86/1.21  
% 1.86/1.22  tff(f_60, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_mcart_1)).
% 1.86/1.22  tff(f_51, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.86/1.22  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.86/1.22  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.86/1.22  tff(c_42, plain, (k1_mcart_1('#skF_5')!='#skF_7' | k2_mcart_1('#skF_5')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.86/1.22  tff(c_65, plain, (k2_mcart_1('#skF_5')!='#skF_8'), inference(splitLeft, [status(thm)], [c_42])).
% 1.86/1.22  tff(c_40, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.86/1.22  tff(c_81, plain, (![A_28, C_29, B_30]: (r2_hidden(k2_mcart_1(A_28), C_29) | ~r2_hidden(A_28, k2_zfmisc_1(B_30, C_29)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.86/1.22  tff(c_84, plain, (r2_hidden(k2_mcart_1('#skF_5'), k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_40, c_81])).
% 1.86/1.22  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.86/1.22  tff(c_87, plain, (k2_mcart_1('#skF_5')='#skF_8'), inference(resolution, [status(thm)], [c_84, c_2])).
% 1.86/1.22  tff(c_91, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_87])).
% 1.86/1.22  tff(c_93, plain, (k2_mcart_1('#skF_5')='#skF_8'), inference(splitRight, [status(thm)], [c_42])).
% 1.86/1.22  tff(c_44, plain, (k1_mcart_1('#skF_5')!='#skF_6' | k2_mcart_1('#skF_5')!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.86/1.22  tff(c_105, plain, (k1_mcart_1('#skF_5')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_44])).
% 1.86/1.22  tff(c_92, plain, (k1_mcart_1('#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_42])).
% 1.86/1.22  tff(c_115, plain, (![A_35, B_36, C_37]: (r2_hidden(k1_mcart_1(A_35), B_36) | ~r2_hidden(A_35, k2_zfmisc_1(B_36, C_37)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.86/1.22  tff(c_118, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_40, c_115])).
% 1.86/1.22  tff(c_124, plain, (![D_41, B_42, A_43]: (D_41=B_42 | D_41=A_43 | ~r2_hidden(D_41, k2_tarski(A_43, B_42)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.86/1.22  tff(c_127, plain, (k1_mcart_1('#skF_5')='#skF_7' | k1_mcart_1('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_118, c_124])).
% 1.86/1.22  tff(c_140, plain, $false, inference(negUnitSimplification, [status(thm)], [c_105, c_92, c_127])).
% 1.86/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.22  
% 1.86/1.22  Inference rules
% 1.86/1.22  ----------------------
% 1.86/1.22  #Ref     : 0
% 1.86/1.22  #Sup     : 20
% 1.86/1.22  #Fact    : 0
% 1.86/1.22  #Define  : 0
% 1.86/1.22  #Split   : 1
% 1.86/1.22  #Chain   : 0
% 1.86/1.22  #Close   : 0
% 1.86/1.22  
% 1.86/1.22  Ordering : KBO
% 1.86/1.22  
% 1.86/1.22  Simplification rules
% 1.86/1.22  ----------------------
% 1.86/1.22  #Subsume      : 1
% 1.86/1.22  #Demod        : 5
% 1.86/1.22  #Tautology    : 13
% 1.86/1.22  #SimpNegUnit  : 2
% 1.86/1.22  #BackRed      : 0
% 1.86/1.22  
% 1.86/1.22  #Partial instantiations: 0
% 1.86/1.22  #Strategies tried      : 1
% 1.86/1.22  
% 1.86/1.22  Timing (in seconds)
% 1.86/1.22  ----------------------
% 1.86/1.23  Preprocessing        : 0.31
% 1.86/1.23  Parsing              : 0.16
% 1.86/1.23  CNF conversion       : 0.02
% 1.86/1.23  Main loop            : 0.12
% 1.86/1.23  Inferencing          : 0.04
% 1.86/1.23  Reduction            : 0.04
% 1.86/1.23  Demodulation         : 0.03
% 1.86/1.23  BG Simplification    : 0.01
% 1.86/1.23  Subsumption          : 0.02
% 1.86/1.23  Abstraction          : 0.01
% 1.86/1.23  MUC search           : 0.00
% 1.86/1.23  Cooper               : 0.00
% 1.86/1.23  Total                : 0.46
% 1.86/1.23  Index Insertion      : 0.00
% 1.86/1.23  Index Deletion       : 0.00
% 1.86/1.23  Index Matching       : 0.00
% 1.86/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

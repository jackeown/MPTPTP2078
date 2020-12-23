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
% DateTime   : Thu Dec  3 10:09:05 EST 2020

% Result     : Theorem 1.70s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   35 (  44 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    4
%              Number of atoms          :   33 (  61 expanded)
%              Number of equality atoms :   21 (  41 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(f_55,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k2_tarski(C,D)))
       => ( k1_mcart_1(A) = B
          & ( k2_mcart_1(A) = C
            | k2_mcart_1(A) = D ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_mcart_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_mcart_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_34,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_54,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_30,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),k2_tarski('#skF_5','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_84,plain,(
    ! [A_29,B_30,C_31] :
      ( k1_mcart_1(A_29) = B_30
      | ~ r2_hidden(A_29,k2_zfmisc_1(k1_tarski(B_30),C_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_87,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_30,c_84])).

tff(c_91,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_87])).

tff(c_92,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_93,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_32,plain,
    ( k2_mcart_1('#skF_3') != '#skF_6'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_99,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_93,c_32])).

tff(c_135,plain,(
    ! [A_42,C_43,B_44] :
      ( r2_hidden(k2_mcart_1(A_42),C_43)
      | ~ r2_hidden(A_42,k2_zfmisc_1(k1_tarski(B_44),C_43)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_139,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k2_tarski('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_30,c_135])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1
      | ~ r2_hidden(D_6,k2_tarski(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_142,plain,
    ( k2_mcart_1('#skF_3') = '#skF_6'
    | k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_139,c_2])).

tff(c_146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_99,c_142])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n025.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:55:35 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.70/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.16  
% 1.70/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.16  %$ r2_hidden > k3_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 1.70/1.16  
% 1.70/1.16  %Foreground sorts:
% 1.70/1.16  
% 1.70/1.16  
% 1.70/1.16  %Background operators:
% 1.70/1.16  
% 1.70/1.16  
% 1.70/1.16  %Foreground operators:
% 1.70/1.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.70/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.70/1.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.70/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.70/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.70/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.70/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.70/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.70/1.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.16  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.70/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.70/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.70/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.16  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.70/1.16  
% 1.70/1.17  tff(f_55, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k2_tarski(C, D))) => ((k1_mcart_1(A) = B) & ((k2_mcart_1(A) = C) | (k2_mcart_1(A) = D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_mcart_1)).
% 1.70/1.17  tff(f_46, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_mcart_1)).
% 1.70/1.17  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.70/1.17  tff(c_34, plain, (k2_mcart_1('#skF_3')!='#skF_5' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.70/1.17  tff(c_54, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_34])).
% 1.70/1.17  tff(c_30, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), k2_tarski('#skF_5', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.70/1.17  tff(c_84, plain, (![A_29, B_30, C_31]: (k1_mcart_1(A_29)=B_30 | ~r2_hidden(A_29, k2_zfmisc_1(k1_tarski(B_30), C_31)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.70/1.17  tff(c_87, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_30, c_84])).
% 1.70/1.17  tff(c_91, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_87])).
% 1.70/1.17  tff(c_92, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_34])).
% 1.70/1.17  tff(c_93, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(splitRight, [status(thm)], [c_34])).
% 1.70/1.17  tff(c_32, plain, (k2_mcart_1('#skF_3')!='#skF_6' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.70/1.17  tff(c_99, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_93, c_32])).
% 1.70/1.17  tff(c_135, plain, (![A_42, C_43, B_44]: (r2_hidden(k2_mcart_1(A_42), C_43) | ~r2_hidden(A_42, k2_zfmisc_1(k1_tarski(B_44), C_43)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.70/1.17  tff(c_139, plain, (r2_hidden(k2_mcart_1('#skF_3'), k2_tarski('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_30, c_135])).
% 1.70/1.17  tff(c_2, plain, (![D_6, B_2, A_1]: (D_6=B_2 | D_6=A_1 | ~r2_hidden(D_6, k2_tarski(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.70/1.17  tff(c_142, plain, (k2_mcart_1('#skF_3')='#skF_6' | k2_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_139, c_2])).
% 1.70/1.17  tff(c_146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_99, c_142])).
% 1.70/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.17  
% 1.70/1.17  Inference rules
% 1.70/1.17  ----------------------
% 1.70/1.17  #Ref     : 0
% 1.70/1.17  #Sup     : 22
% 1.70/1.17  #Fact    : 0
% 1.70/1.17  #Define  : 0
% 1.70/1.17  #Split   : 1
% 1.70/1.17  #Chain   : 0
% 1.70/1.17  #Close   : 0
% 1.70/1.17  
% 1.70/1.17  Ordering : KBO
% 1.70/1.17  
% 1.70/1.17  Simplification rules
% 1.70/1.17  ----------------------
% 1.70/1.17  #Subsume      : 1
% 1.70/1.17  #Demod        : 3
% 1.70/1.17  #Tautology    : 16
% 1.70/1.17  #SimpNegUnit  : 2
% 1.70/1.17  #BackRed      : 0
% 1.70/1.17  
% 1.70/1.17  #Partial instantiations: 0
% 1.70/1.17  #Strategies tried      : 1
% 1.70/1.17  
% 1.70/1.17  Timing (in seconds)
% 1.70/1.17  ----------------------
% 1.70/1.17  Preprocessing        : 0.29
% 1.70/1.17  Parsing              : 0.15
% 1.70/1.17  CNF conversion       : 0.02
% 1.70/1.17  Main loop            : 0.12
% 1.70/1.17  Inferencing          : 0.04
% 1.70/1.17  Reduction            : 0.04
% 1.70/1.17  Demodulation         : 0.03
% 1.70/1.17  BG Simplification    : 0.01
% 1.70/1.17  Subsumption          : 0.02
% 1.70/1.17  Abstraction          : 0.01
% 1.70/1.17  MUC search           : 0.00
% 1.70/1.17  Cooper               : 0.00
% 1.70/1.18  Total                : 0.43
% 1.70/1.18  Index Insertion      : 0.00
% 1.70/1.18  Index Deletion       : 0.00
% 1.70/1.18  Index Matching       : 0.00
% 1.70/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

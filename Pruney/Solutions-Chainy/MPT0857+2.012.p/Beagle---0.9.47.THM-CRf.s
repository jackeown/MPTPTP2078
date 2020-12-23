%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:55 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   41 (  68 expanded)
%              Number of leaves         :   20 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   49 ( 109 expanded)
%              Number of equality atoms :   14 (  38 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_mcart_1,type,(
    k2_mcart_1: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
       => ( r2_hidden(k1_mcart_1(A),B)
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_mcart_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_57,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) )
     => ( ! [D,E] : A != k4_tarski(D,E)
        | r2_hidden(A,k2_zfmisc_1(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t11_mcart_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),C))
     => ( k1_mcart_1(A) = B
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_mcart_1)).

tff(c_22,plain,
    ( k2_mcart_1('#skF_1') != '#skF_3'
    | ~ r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_53,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_24,plain,(
    r2_hidden('#skF_1',k2_zfmisc_1('#skF_2',k1_tarski('#skF_3'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_64,plain,(
    ! [A_32,B_33,C_34] :
      ( r2_hidden(k1_mcart_1(A_32),B_33)
      | ~ r2_hidden(A_32,k2_zfmisc_1(B_33,C_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_66,plain,(
    r2_hidden(k1_mcart_1('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_24,c_64])).

tff(c_70,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_66])).

tff(c_71,plain,(
    k2_mcart_1('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_88,plain,(
    ! [A_43,C_44,B_45] :
      ( r2_hidden(k2_mcart_1(A_43),C_44)
      | ~ r2_hidden(A_43,k2_zfmisc_1(B_45,C_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_91,plain,(
    r2_hidden(k2_mcart_1('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_88])).

tff(c_18,plain,(
    ! [A_20,B_21] : k1_mcart_1(k4_tarski(A_20,B_21)) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_20,B_21] : k2_mcart_1(k4_tarski(A_20,B_21)) = B_21 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12,plain,(
    ! [D_15,E_16,B_11,C_12] :
      ( r2_hidden(k4_tarski(D_15,E_16),k2_zfmisc_1(B_11,C_12))
      | ~ r2_hidden(k2_mcart_1(k4_tarski(D_15,E_16)),C_12)
      | ~ r2_hidden(k1_mcart_1(k4_tarski(D_15,E_16)),B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_101,plain,(
    ! [D_49,E_50,B_51,C_52] :
      ( r2_hidden(k4_tarski(D_49,E_50),k2_zfmisc_1(B_51,C_52))
      | ~ r2_hidden(E_50,C_52)
      | ~ r2_hidden(D_49,B_51) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_20,c_12])).

tff(c_16,plain,(
    ! [A_17,B_18,C_19] :
      ( k1_mcart_1(A_17) = B_18
      | ~ r2_hidden(A_17,k2_zfmisc_1(k1_tarski(B_18),C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_107,plain,(
    ! [D_49,E_50,B_18,C_52] :
      ( k1_mcart_1(k4_tarski(D_49,E_50)) = B_18
      | ~ r2_hidden(E_50,C_52)
      | ~ r2_hidden(D_49,k1_tarski(B_18)) ) ),
    inference(resolution,[status(thm)],[c_101,c_16])).

tff(c_113,plain,(
    ! [D_49,B_18,E_50,C_52] :
      ( D_49 = B_18
      | ~ r2_hidden(E_50,C_52)
      | ~ r2_hidden(D_49,k1_tarski(B_18)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_107])).

tff(c_116,plain,(
    ! [E_50,C_52] : ~ r2_hidden(E_50,C_52) ),
    inference(splitLeft,[status(thm)],[c_113])).

tff(c_123,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_116,c_91])).

tff(c_125,plain,(
    ! [D_53,B_54] :
      ( D_53 = B_54
      | ~ r2_hidden(D_53,k1_tarski(B_54)) ) ),
    inference(splitRight,[status(thm)],[c_113])).

tff(c_128,plain,(
    k2_mcart_1('#skF_1') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_91,c_125])).

tff(c_132,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_71,c_128])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n022.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:52:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.13  
% 1.76/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.14  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_2 > #skF_3 > #skF_1
% 1.76/1.14  
% 1.76/1.14  %Foreground sorts:
% 1.76/1.14  
% 1.76/1.14  
% 1.76/1.14  %Background operators:
% 1.76/1.14  
% 1.76/1.14  
% 1.76/1.14  %Foreground operators:
% 1.76/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.14  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.76/1.14  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.76/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.76/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.76/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.76/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.76/1.14  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.76/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.14  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.76/1.14  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.76/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.14  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.76/1.14  
% 1.76/1.15  tff(f_64, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_mcart_1)).
% 1.76/1.15  tff(f_37, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.76/1.15  tff(f_57, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.76/1.15  tff(f_47, axiom, (![A, B, C]: ((r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)) => ((![D, E]: ~(A = k4_tarski(D, E))) | r2_hidden(A, k2_zfmisc_1(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t11_mcart_1)).
% 1.76/1.15  tff(f_53, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), C)) => ((k1_mcart_1(A) = B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_mcart_1)).
% 1.76/1.15  tff(c_22, plain, (k2_mcart_1('#skF_1')!='#skF_3' | ~r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.76/1.15  tff(c_53, plain, (~r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(splitLeft, [status(thm)], [c_22])).
% 1.76/1.15  tff(c_24, plain, (r2_hidden('#skF_1', k2_zfmisc_1('#skF_2', k1_tarski('#skF_3')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 1.76/1.15  tff(c_64, plain, (![A_32, B_33, C_34]: (r2_hidden(k1_mcart_1(A_32), B_33) | ~r2_hidden(A_32, k2_zfmisc_1(B_33, C_34)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.76/1.15  tff(c_66, plain, (r2_hidden(k1_mcart_1('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_24, c_64])).
% 1.76/1.15  tff(c_70, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_66])).
% 1.76/1.15  tff(c_71, plain, (k2_mcart_1('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_22])).
% 1.76/1.15  tff(c_88, plain, (![A_43, C_44, B_45]: (r2_hidden(k2_mcart_1(A_43), C_44) | ~r2_hidden(A_43, k2_zfmisc_1(B_45, C_44)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.76/1.15  tff(c_91, plain, (r2_hidden(k2_mcart_1('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_88])).
% 1.76/1.15  tff(c_18, plain, (![A_20, B_21]: (k1_mcart_1(k4_tarski(A_20, B_21))=A_20)), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.76/1.15  tff(c_20, plain, (![A_20, B_21]: (k2_mcart_1(k4_tarski(A_20, B_21))=B_21)), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.76/1.15  tff(c_12, plain, (![D_15, E_16, B_11, C_12]: (r2_hidden(k4_tarski(D_15, E_16), k2_zfmisc_1(B_11, C_12)) | ~r2_hidden(k2_mcart_1(k4_tarski(D_15, E_16)), C_12) | ~r2_hidden(k1_mcart_1(k4_tarski(D_15, E_16)), B_11))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.76/1.15  tff(c_101, plain, (![D_49, E_50, B_51, C_52]: (r2_hidden(k4_tarski(D_49, E_50), k2_zfmisc_1(B_51, C_52)) | ~r2_hidden(E_50, C_52) | ~r2_hidden(D_49, B_51))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_20, c_12])).
% 1.76/1.15  tff(c_16, plain, (![A_17, B_18, C_19]: (k1_mcart_1(A_17)=B_18 | ~r2_hidden(A_17, k2_zfmisc_1(k1_tarski(B_18), C_19)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.76/1.15  tff(c_107, plain, (![D_49, E_50, B_18, C_52]: (k1_mcart_1(k4_tarski(D_49, E_50))=B_18 | ~r2_hidden(E_50, C_52) | ~r2_hidden(D_49, k1_tarski(B_18)))), inference(resolution, [status(thm)], [c_101, c_16])).
% 1.76/1.15  tff(c_113, plain, (![D_49, B_18, E_50, C_52]: (D_49=B_18 | ~r2_hidden(E_50, C_52) | ~r2_hidden(D_49, k1_tarski(B_18)))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_107])).
% 1.76/1.15  tff(c_116, plain, (![E_50, C_52]: (~r2_hidden(E_50, C_52))), inference(splitLeft, [status(thm)], [c_113])).
% 1.76/1.15  tff(c_123, plain, $false, inference(negUnitSimplification, [status(thm)], [c_116, c_91])).
% 1.76/1.15  tff(c_125, plain, (![D_53, B_54]: (D_53=B_54 | ~r2_hidden(D_53, k1_tarski(B_54)))), inference(splitRight, [status(thm)], [c_113])).
% 1.76/1.15  tff(c_128, plain, (k2_mcart_1('#skF_1')='#skF_3'), inference(resolution, [status(thm)], [c_91, c_125])).
% 1.76/1.15  tff(c_132, plain, $false, inference(negUnitSimplification, [status(thm)], [c_71, c_128])).
% 1.76/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.15  
% 1.76/1.15  Inference rules
% 1.76/1.15  ----------------------
% 1.76/1.15  #Ref     : 0
% 1.76/1.15  #Sup     : 19
% 1.76/1.15  #Fact    : 0
% 1.76/1.15  #Define  : 0
% 1.76/1.15  #Split   : 2
% 1.76/1.15  #Chain   : 0
% 1.76/1.15  #Close   : 0
% 1.76/1.15  
% 1.76/1.15  Ordering : KBO
% 1.76/1.15  
% 1.76/1.15  Simplification rules
% 1.76/1.15  ----------------------
% 1.76/1.15  #Subsume      : 5
% 1.76/1.15  #Demod        : 6
% 1.76/1.15  #Tautology    : 15
% 1.76/1.15  #SimpNegUnit  : 8
% 1.76/1.15  #BackRed      : 3
% 1.76/1.15  
% 1.76/1.15  #Partial instantiations: 0
% 1.76/1.15  #Strategies tried      : 1
% 1.76/1.15  
% 1.76/1.15  Timing (in seconds)
% 1.76/1.15  ----------------------
% 1.76/1.15  Preprocessing        : 0.28
% 1.76/1.15  Parsing              : 0.15
% 1.76/1.15  CNF conversion       : 0.02
% 1.76/1.15  Main loop            : 0.11
% 1.76/1.15  Inferencing          : 0.04
% 1.76/1.15  Reduction            : 0.04
% 1.76/1.15  Demodulation         : 0.03
% 1.76/1.15  BG Simplification    : 0.01
% 1.83/1.15  Subsumption          : 0.01
% 1.83/1.15  Abstraction          : 0.01
% 1.83/1.15  MUC search           : 0.00
% 1.83/1.15  Cooper               : 0.00
% 1.83/1.15  Total                : 0.41
% 1.83/1.15  Index Insertion      : 0.00
% 1.83/1.15  Index Deletion       : 0.00
% 1.83/1.15  Index Matching       : 0.00
% 1.83/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

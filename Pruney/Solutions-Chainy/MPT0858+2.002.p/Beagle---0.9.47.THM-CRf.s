%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:56 EST 2020

% Result     : Theorem 1.59s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   32 (  44 expanded)
%              Number of leaves         :   18 (  24 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  48 expanded)
%              Number of equality atoms :   18 (  34 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_45,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k1_tarski(C)))
       => ( k1_mcart_1(A) = B
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_mcart_1)).

tff(f_34,axiom,(
    ! [A,B] : k2_zfmisc_1(k1_tarski(A),k1_tarski(B)) = k1_tarski(k4_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t35_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_38,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_20,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_53,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_14,plain,(
    ! [A_6,B_7] : k2_zfmisc_1(k1_tarski(A_6),k1_tarski(B_7)) = k1_tarski(k4_tarski(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_22,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),k1_tarski('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_23,plain,(
    r2_hidden('#skF_3',k1_tarski(k4_tarski('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_22])).

tff(c_43,plain,(
    ! [C_15,A_16] :
      ( C_15 = A_16
      | ~ r2_hidden(C_15,k1_tarski(A_16)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_50,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_23,c_43])).

tff(c_16,plain,(
    ! [A_8,B_9] : k1_mcart_1(k4_tarski(A_8,B_9)) = A_8 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_59,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_16])).

tff(c_66,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_53,c_59])).

tff(c_67,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_18,plain,(
    ! [A_8,B_9] : k2_mcart_1(k4_tarski(A_8,B_9)) = B_9 ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_81,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_18])).

tff(c_86,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_81])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:33:07 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.59/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.17  
% 1.59/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.59/1.18  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.59/1.18  
% 1.59/1.18  %Foreground sorts:
% 1.59/1.18  
% 1.59/1.18  
% 1.59/1.18  %Background operators:
% 1.59/1.18  
% 1.59/1.18  
% 1.59/1.18  %Foreground operators:
% 1.59/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.59/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.59/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.59/1.18  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.59/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.59/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.59/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.59/1.18  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.59/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.59/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.59/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.59/1.18  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.59/1.18  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.59/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.59/1.18  
% 1.76/1.19  tff(f_45, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k1_tarski(C))) => ((k1_mcart_1(A) = B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_mcart_1)).
% 1.76/1.19  tff(f_34, axiom, (![A, B]: (k2_zfmisc_1(k1_tarski(A), k1_tarski(B)) = k1_tarski(k4_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t35_zfmisc_1)).
% 1.76/1.19  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.76/1.19  tff(f_38, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.76/1.19  tff(c_20, plain, (k2_mcart_1('#skF_3')!='#skF_5' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.76/1.19  tff(c_53, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_20])).
% 1.76/1.19  tff(c_14, plain, (![A_6, B_7]: (k2_zfmisc_1(k1_tarski(A_6), k1_tarski(B_7))=k1_tarski(k4_tarski(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.76/1.19  tff(c_22, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), k1_tarski('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.76/1.19  tff(c_23, plain, (r2_hidden('#skF_3', k1_tarski(k4_tarski('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_22])).
% 1.76/1.19  tff(c_43, plain, (![C_15, A_16]: (C_15=A_16 | ~r2_hidden(C_15, k1_tarski(A_16)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.76/1.19  tff(c_50, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(resolution, [status(thm)], [c_23, c_43])).
% 1.76/1.19  tff(c_16, plain, (![A_8, B_9]: (k1_mcart_1(k4_tarski(A_8, B_9))=A_8)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.76/1.19  tff(c_59, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_50, c_16])).
% 1.76/1.19  tff(c_66, plain, $false, inference(negUnitSimplification, [status(thm)], [c_53, c_59])).
% 1.76/1.19  tff(c_67, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_20])).
% 1.76/1.19  tff(c_18, plain, (![A_8, B_9]: (k2_mcart_1(k4_tarski(A_8, B_9))=B_9)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.76/1.19  tff(c_81, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_50, c_18])).
% 1.76/1.19  tff(c_86, plain, $false, inference(negUnitSimplification, [status(thm)], [c_67, c_81])).
% 1.76/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.76/1.19  
% 1.76/1.19  Inference rules
% 1.76/1.19  ----------------------
% 1.76/1.19  #Ref     : 0
% 1.76/1.19  #Sup     : 16
% 1.76/1.19  #Fact    : 0
% 1.76/1.19  #Define  : 0
% 1.76/1.19  #Split   : 1
% 1.76/1.19  #Chain   : 0
% 1.76/1.19  #Close   : 0
% 1.76/1.19  
% 1.76/1.19  Ordering : KBO
% 1.76/1.19  
% 1.76/1.19  Simplification rules
% 1.76/1.19  ----------------------
% 1.76/1.19  #Subsume      : 0
% 1.76/1.19  #Demod        : 6
% 1.76/1.19  #Tautology    : 12
% 1.76/1.19  #SimpNegUnit  : 2
% 1.76/1.19  #BackRed      : 2
% 1.76/1.19  
% 1.76/1.19  #Partial instantiations: 0
% 1.76/1.19  #Strategies tried      : 1
% 1.76/1.19  
% 1.76/1.19  Timing (in seconds)
% 1.76/1.19  ----------------------
% 1.76/1.19  Preprocessing        : 0.28
% 1.76/1.19  Parsing              : 0.15
% 1.76/1.19  CNF conversion       : 0.02
% 1.76/1.19  Main loop            : 0.08
% 1.76/1.19  Inferencing          : 0.02
% 1.76/1.19  Reduction            : 0.03
% 1.76/1.19  Demodulation         : 0.02
% 1.76/1.19  BG Simplification    : 0.01
% 1.76/1.19  Subsumption          : 0.01
% 1.76/1.19  Abstraction          : 0.00
% 1.76/1.19  MUC search           : 0.00
% 1.76/1.19  Cooper               : 0.00
% 1.76/1.19  Total                : 0.40
% 1.76/1.19  Index Insertion      : 0.00
% 1.76/1.19  Index Deletion       : 0.00
% 1.76/1.19  Index Matching       : 0.00
% 1.76/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

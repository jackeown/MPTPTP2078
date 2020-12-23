%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:56 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   42 (  57 expanded)
%              Number of leaves         :   20 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   35 (  62 expanded)
%              Number of equality atoms :   27 (  48 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_49,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k1_tarski(C)))
       => ( k1_mcart_1(A) = B
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_mcart_1)).

tff(f_34,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_38,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_24,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_61,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_14,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    ! [A_28,B_29,C_30] : k2_zfmisc_1(k1_tarski(A_28),k2_tarski(B_29,C_30)) = k2_tarski(k4_tarski(A_28,B_29),k4_tarski(A_28,C_30)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_89,plain,(
    ! [A_28,C_30] : k2_zfmisc_1(k1_tarski(A_28),k2_tarski(C_30,C_30)) = k1_tarski(k4_tarski(A_28,C_30)) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_14])).

tff(c_108,plain,(
    ! [A_28,C_30] : k2_zfmisc_1(k1_tarski(A_28),k1_tarski(C_30)) = k1_tarski(k4_tarski(A_28,C_30)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_89])).

tff(c_26,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),k1_tarski('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_113,plain,(
    r2_hidden('#skF_3',k1_tarski(k4_tarski('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_108,c_26])).

tff(c_2,plain,(
    ! [C_5,A_1] :
      ( C_5 = A_1
      | ~ r2_hidden(C_5,k1_tarski(A_1)) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_126,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_113,c_2])).

tff(c_20,plain,(
    ! [A_10,B_11] : k1_mcart_1(k4_tarski(A_10,B_11)) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_188,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_126,c_20])).

tff(c_192,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_61,c_188])).

tff(c_193,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_207,plain,(
    ! [A_42,B_43,C_44] : k2_zfmisc_1(k2_tarski(A_42,B_43),k1_tarski(C_44)) = k2_tarski(k4_tarski(A_42,C_44),k4_tarski(B_43,C_44)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_220,plain,(
    ! [B_43,C_44] : k2_zfmisc_1(k2_tarski(B_43,B_43),k1_tarski(C_44)) = k1_tarski(k4_tarski(B_43,C_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_207,c_14])).

tff(c_239,plain,(
    ! [B_43,C_44] : k2_zfmisc_1(k1_tarski(B_43),k1_tarski(C_44)) = k1_tarski(k4_tarski(B_43,C_44)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_220])).

tff(c_244,plain,(
    r2_hidden('#skF_3',k1_tarski(k4_tarski('#skF_4','#skF_5'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_239,c_26])).

tff(c_310,plain,(
    k4_tarski('#skF_4','#skF_5') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_244,c_2])).

tff(c_22,plain,(
    ! [A_10,B_11] : k2_mcart_1(k4_tarski(A_10,B_11)) = B_11 ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_316,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_22])).

tff(c_323,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_193,c_316])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:52:57 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.26  
% 1.99/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.26  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_5 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.99/1.26  
% 1.99/1.26  %Foreground sorts:
% 1.99/1.26  
% 1.99/1.26  
% 1.99/1.26  %Background operators:
% 1.99/1.26  
% 1.99/1.26  
% 1.99/1.26  %Foreground operators:
% 1.99/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.26  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.99/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.26  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.26  tff('#skF_3', type, '#skF_3': $i).
% 1.99/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.26  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.99/1.26  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.99/1.26  tff('#skF_4', type, '#skF_4': $i).
% 1.99/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.26  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.99/1.26  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.99/1.26  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.99/1.26  
% 1.99/1.27  tff(f_49, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k1_tarski(C))) => ((k1_mcart_1(A) = B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_mcart_1)).
% 1.99/1.27  tff(f_34, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.99/1.27  tff(f_38, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 1.99/1.27  tff(f_32, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.99/1.27  tff(f_42, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.99/1.27  tff(c_24, plain, (k2_mcart_1('#skF_3')!='#skF_5' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.99/1.27  tff(c_61, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_24])).
% 1.99/1.27  tff(c_14, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.99/1.27  tff(c_76, plain, (![A_28, B_29, C_30]: (k2_zfmisc_1(k1_tarski(A_28), k2_tarski(B_29, C_30))=k2_tarski(k4_tarski(A_28, B_29), k4_tarski(A_28, C_30)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.99/1.27  tff(c_89, plain, (![A_28, C_30]: (k2_zfmisc_1(k1_tarski(A_28), k2_tarski(C_30, C_30))=k1_tarski(k4_tarski(A_28, C_30)))), inference(superposition, [status(thm), theory('equality')], [c_76, c_14])).
% 1.99/1.27  tff(c_108, plain, (![A_28, C_30]: (k2_zfmisc_1(k1_tarski(A_28), k1_tarski(C_30))=k1_tarski(k4_tarski(A_28, C_30)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_89])).
% 1.99/1.27  tff(c_26, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), k1_tarski('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.99/1.27  tff(c_113, plain, (r2_hidden('#skF_3', k1_tarski(k4_tarski('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_108, c_26])).
% 1.99/1.27  tff(c_2, plain, (![C_5, A_1]: (C_5=A_1 | ~r2_hidden(C_5, k1_tarski(A_1)))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.99/1.27  tff(c_126, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(resolution, [status(thm)], [c_113, c_2])).
% 1.99/1.27  tff(c_20, plain, (![A_10, B_11]: (k1_mcart_1(k4_tarski(A_10, B_11))=A_10)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.99/1.27  tff(c_188, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_126, c_20])).
% 1.99/1.27  tff(c_192, plain, $false, inference(negUnitSimplification, [status(thm)], [c_61, c_188])).
% 1.99/1.27  tff(c_193, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_24])).
% 1.99/1.27  tff(c_207, plain, (![A_42, B_43, C_44]: (k2_zfmisc_1(k2_tarski(A_42, B_43), k1_tarski(C_44))=k2_tarski(k4_tarski(A_42, C_44), k4_tarski(B_43, C_44)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.99/1.27  tff(c_220, plain, (![B_43, C_44]: (k2_zfmisc_1(k2_tarski(B_43, B_43), k1_tarski(C_44))=k1_tarski(k4_tarski(B_43, C_44)))), inference(superposition, [status(thm), theory('equality')], [c_207, c_14])).
% 1.99/1.27  tff(c_239, plain, (![B_43, C_44]: (k2_zfmisc_1(k1_tarski(B_43), k1_tarski(C_44))=k1_tarski(k4_tarski(B_43, C_44)))), inference(demodulation, [status(thm), theory('equality')], [c_14, c_220])).
% 1.99/1.27  tff(c_244, plain, (r2_hidden('#skF_3', k1_tarski(k4_tarski('#skF_4', '#skF_5')))), inference(demodulation, [status(thm), theory('equality')], [c_239, c_26])).
% 1.99/1.27  tff(c_310, plain, (k4_tarski('#skF_4', '#skF_5')='#skF_3'), inference(resolution, [status(thm)], [c_244, c_2])).
% 1.99/1.27  tff(c_22, plain, (![A_10, B_11]: (k2_mcart_1(k4_tarski(A_10, B_11))=B_11)), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.99/1.27  tff(c_316, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_310, c_22])).
% 1.99/1.27  tff(c_323, plain, $false, inference(negUnitSimplification, [status(thm)], [c_193, c_316])).
% 1.99/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.99/1.27  
% 1.99/1.27  Inference rules
% 1.99/1.27  ----------------------
% 1.99/1.27  #Ref     : 0
% 1.99/1.27  #Sup     : 70
% 1.99/1.27  #Fact    : 0
% 1.99/1.27  #Define  : 0
% 1.99/1.27  #Split   : 1
% 1.99/1.27  #Chain   : 0
% 1.99/1.27  #Close   : 0
% 1.99/1.27  
% 1.99/1.27  Ordering : KBO
% 1.99/1.27  
% 1.99/1.27  Simplification rules
% 1.99/1.27  ----------------------
% 1.99/1.27  #Subsume      : 0
% 1.99/1.27  #Demod        : 32
% 1.99/1.27  #Tautology    : 43
% 1.99/1.27  #SimpNegUnit  : 2
% 1.99/1.27  #BackRed      : 4
% 1.99/1.27  
% 1.99/1.27  #Partial instantiations: 0
% 1.99/1.27  #Strategies tried      : 1
% 1.99/1.27  
% 1.99/1.27  Timing (in seconds)
% 1.99/1.27  ----------------------
% 1.99/1.27  Preprocessing        : 0.28
% 1.99/1.27  Parsing              : 0.15
% 1.99/1.27  CNF conversion       : 0.02
% 1.99/1.27  Main loop            : 0.20
% 1.99/1.27  Inferencing          : 0.08
% 1.99/1.27  Reduction            : 0.06
% 1.99/1.27  Demodulation         : 0.05
% 1.99/1.27  BG Simplification    : 0.01
% 1.99/1.28  Subsumption          : 0.03
% 1.99/1.28  Abstraction          : 0.02
% 1.99/1.28  MUC search           : 0.00
% 1.99/1.28  Cooper               : 0.00
% 1.99/1.28  Total                : 0.50
% 1.99/1.28  Index Insertion      : 0.00
% 1.99/1.28  Index Deletion       : 0.00
% 1.99/1.28  Index Matching       : 0.00
% 1.99/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------

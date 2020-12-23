%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:56 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   38 (  53 expanded)
%              Number of leaves         :   21 (  29 expanded)
%              Depth                    :    4
%              Number of atoms          :   39 (  72 expanded)
%              Number of equality atoms :   21 (  44 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

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
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(k1_tarski(B),k1_tarski(C)))
       => ( k1_mcart_1(A) = B
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t14_mcart_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_32,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_54,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_34,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k1_tarski('#skF_4'),k1_tarski('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_107,plain,(
    ! [A_39,B_40,C_41] :
      ( r2_hidden(k1_mcart_1(A_39),B_40)
      | ~ r2_hidden(A_39,k2_zfmisc_1(B_40,C_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_110,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_34,c_107])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_73,plain,(
    ! [D_31,B_32,A_33] :
      ( D_31 = B_32
      | D_31 = A_33
      | ~ r2_hidden(D_31,k2_tarski(A_33,B_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_82,plain,(
    ! [D_31,A_7] :
      ( D_31 = A_7
      | D_31 = A_7
      | ~ r2_hidden(D_31,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_73])).

tff(c_122,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_110,c_82])).

tff(c_126,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_54,c_122])).

tff(c_127,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_176,plain,(
    ! [A_59,C_60,B_61] :
      ( r2_hidden(k2_mcart_1(A_59),C_60)
      | ~ r2_hidden(A_59,k2_zfmisc_1(B_61,C_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_179,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_34,c_176])).

tff(c_151,plain,(
    ! [D_51,B_52,A_53] :
      ( D_51 = B_52
      | D_51 = A_53
      | ~ r2_hidden(D_51,k2_tarski(A_53,B_52)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_160,plain,(
    ! [D_51,A_7] :
      ( D_51 = A_7
      | D_51 = A_7
      | ~ r2_hidden(D_51,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_151])).

tff(c_182,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_179,c_160])).

tff(c_186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_127,c_127,c_182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n023.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 14:02:51 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.21  
% 1.89/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.21  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.89/1.21  
% 1.89/1.21  %Foreground sorts:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Background operators:
% 1.89/1.21  
% 1.89/1.21  
% 1.89/1.21  %Foreground operators:
% 1.89/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.89/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.89/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.89/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.89/1.21  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.21  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.89/1.21  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.89/1.21  tff('#skF_4', type, '#skF_4': $i).
% 1.89/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.21  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.89/1.21  
% 1.89/1.22  tff(f_55, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(k1_tarski(B), k1_tarski(C))) => ((k1_mcart_1(A) = B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t14_mcart_1)).
% 1.89/1.22  tff(f_48, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.89/1.22  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.89/1.22  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.89/1.22  tff(c_32, plain, (k2_mcart_1('#skF_3')!='#skF_5' | k1_mcart_1('#skF_3')!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.89/1.22  tff(c_54, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitLeft, [status(thm)], [c_32])).
% 1.89/1.22  tff(c_34, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k1_tarski('#skF_4'), k1_tarski('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_55])).
% 1.89/1.22  tff(c_107, plain, (![A_39, B_40, C_41]: (r2_hidden(k1_mcart_1(A_39), B_40) | ~r2_hidden(A_39, k2_zfmisc_1(B_40, C_41)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.89/1.22  tff(c_110, plain, (r2_hidden(k1_mcart_1('#skF_3'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_34, c_107])).
% 1.89/1.22  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.89/1.22  tff(c_73, plain, (![D_31, B_32, A_33]: (D_31=B_32 | D_31=A_33 | ~r2_hidden(D_31, k2_tarski(A_33, B_32)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.89/1.22  tff(c_82, plain, (![D_31, A_7]: (D_31=A_7 | D_31=A_7 | ~r2_hidden(D_31, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_73])).
% 1.89/1.22  tff(c_122, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_110, c_82])).
% 1.89/1.22  tff(c_126, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_54, c_122])).
% 1.89/1.22  tff(c_127, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_32])).
% 1.89/1.22  tff(c_176, plain, (![A_59, C_60, B_61]: (r2_hidden(k2_mcart_1(A_59), C_60) | ~r2_hidden(A_59, k2_zfmisc_1(B_61, C_60)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.89/1.22  tff(c_179, plain, (r2_hidden(k2_mcart_1('#skF_3'), k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_34, c_176])).
% 1.89/1.22  tff(c_151, plain, (![D_51, B_52, A_53]: (D_51=B_52 | D_51=A_53 | ~r2_hidden(D_51, k2_tarski(A_53, B_52)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.89/1.22  tff(c_160, plain, (![D_51, A_7]: (D_51=A_7 | D_51=A_7 | ~r2_hidden(D_51, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_151])).
% 1.89/1.22  tff(c_182, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_179, c_160])).
% 1.89/1.22  tff(c_186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_127, c_127, c_182])).
% 1.89/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.22  
% 1.89/1.22  Inference rules
% 1.89/1.22  ----------------------
% 1.89/1.22  #Ref     : 0
% 1.89/1.22  #Sup     : 33
% 1.89/1.22  #Fact    : 0
% 1.89/1.22  #Define  : 0
% 1.89/1.22  #Split   : 1
% 1.89/1.22  #Chain   : 0
% 1.89/1.22  #Close   : 0
% 1.89/1.22  
% 1.89/1.22  Ordering : KBO
% 1.89/1.22  
% 1.89/1.22  Simplification rules
% 1.89/1.22  ----------------------
% 1.89/1.22  #Subsume      : 0
% 1.89/1.22  #Demod        : 5
% 1.89/1.22  #Tautology    : 25
% 1.89/1.22  #SimpNegUnit  : 2
% 1.89/1.22  #BackRed      : 1
% 1.89/1.22  
% 1.89/1.22  #Partial instantiations: 0
% 1.89/1.22  #Strategies tried      : 1
% 1.89/1.22  
% 1.89/1.22  Timing (in seconds)
% 1.89/1.22  ----------------------
% 1.97/1.22  Preprocessing        : 0.32
% 1.97/1.22  Parsing              : 0.16
% 1.97/1.22  CNF conversion       : 0.02
% 1.97/1.22  Main loop            : 0.13
% 1.97/1.22  Inferencing          : 0.05
% 1.97/1.22  Reduction            : 0.04
% 1.97/1.22  Demodulation         : 0.03
% 1.97/1.22  BG Simplification    : 0.01
% 1.97/1.22  Subsumption          : 0.02
% 1.97/1.22  Abstraction          : 0.01
% 1.97/1.22  MUC search           : 0.00
% 1.97/1.22  Cooper               : 0.00
% 1.97/1.22  Total                : 0.47
% 1.97/1.22  Index Insertion      : 0.00
% 1.97/1.22  Index Deletion       : 0.00
% 1.97/1.22  Index Matching       : 0.00
% 1.97/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------

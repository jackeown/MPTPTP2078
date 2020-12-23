%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:02 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.91s
% Verified   : 
% Statistics : Number of formulae       :   36 (  46 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    4
%              Number of atoms          :   38 (  69 expanded)
%              Number of equality atoms :   22 (  46 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

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

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_mcart_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
     => ( r2_hidden(k1_mcart_1(A),B)
        & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_32,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_54,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_30,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_55,plain,(
    ! [A_20,C_21,B_22] :
      ( k2_mcart_1(A_20) = C_21
      | ~ r2_hidden(A_20,k2_zfmisc_1(B_22,k1_tarski(C_21))) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_58,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_30,c_55])).

tff(c_62,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_58])).

tff(c_64,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_34,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_65,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_71,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_65])).

tff(c_72,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_63,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_85,plain,(
    ! [A_26,B_27,C_28] :
      ( r2_hidden(k1_mcart_1(A_26),B_27)
      | ~ r2_hidden(A_26,k2_zfmisc_1(B_27,C_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_88,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_30,c_85])).

tff(c_89,plain,(
    ! [D_29,B_30,A_31] :
      ( D_29 = B_30
      | D_29 = A_31
      | ~ r2_hidden(D_29,k2_tarski(A_31,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_92,plain,
    ( k1_mcart_1('#skF_3') = '#skF_5'
    | k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_88,c_89])).

tff(c_105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_72,c_63,c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 16:56:24 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.22  
% 1.80/1.22  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.22  %$ r2_hidden > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 1.80/1.22  
% 1.80/1.22  %Foreground sorts:
% 1.80/1.22  
% 1.80/1.22  
% 1.80/1.22  %Background operators:
% 1.80/1.22  
% 1.80/1.22  
% 1.80/1.22  %Foreground operators:
% 1.80/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.80/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.80/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.80/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.80/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.80/1.22  tff('#skF_5', type, '#skF_5': $i).
% 1.80/1.22  tff('#skF_6', type, '#skF_6': $i).
% 1.80/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.80/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.80/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.80/1.22  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.80/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.80/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.80/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.80/1.22  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.80/1.22  
% 1.91/1.23  tff(f_57, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_mcart_1)).
% 1.91/1.23  tff(f_48, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_mcart_1)).
% 1.91/1.23  tff(f_42, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.91/1.23  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.91/1.23  tff(c_32, plain, (k1_mcart_1('#skF_3')!='#skF_5' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.91/1.23  tff(c_54, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitLeft, [status(thm)], [c_32])).
% 1.91/1.23  tff(c_30, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.91/1.23  tff(c_55, plain, (![A_20, C_21, B_22]: (k2_mcart_1(A_20)=C_21 | ~r2_hidden(A_20, k2_zfmisc_1(B_22, k1_tarski(C_21))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.91/1.23  tff(c_58, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_30, c_55])).
% 1.91/1.23  tff(c_62, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_58])).
% 1.91/1.23  tff(c_64, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_32])).
% 1.91/1.23  tff(c_34, plain, (k1_mcart_1('#skF_3')!='#skF_4' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_57])).
% 1.91/1.23  tff(c_65, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitLeft, [status(thm)], [c_34])).
% 1.91/1.23  tff(c_71, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_64, c_65])).
% 1.91/1.23  tff(c_72, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitRight, [status(thm)], [c_34])).
% 1.91/1.23  tff(c_63, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_32])).
% 1.91/1.23  tff(c_85, plain, (![A_26, B_27, C_28]: (r2_hidden(k1_mcart_1(A_26), B_27) | ~r2_hidden(A_26, k2_zfmisc_1(B_27, C_28)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.91/1.23  tff(c_88, plain, (r2_hidden(k1_mcart_1('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_30, c_85])).
% 1.91/1.23  tff(c_89, plain, (![D_29, B_30, A_31]: (D_29=B_30 | D_29=A_31 | ~r2_hidden(D_29, k2_tarski(A_31, B_30)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.91/1.23  tff(c_92, plain, (k1_mcart_1('#skF_3')='#skF_5' | k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_88, c_89])).
% 1.91/1.23  tff(c_105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_72, c_63, c_92])).
% 1.91/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.91/1.23  
% 1.91/1.23  Inference rules
% 1.91/1.23  ----------------------
% 1.91/1.23  #Ref     : 0
% 1.91/1.23  #Sup     : 15
% 1.91/1.23  #Fact    : 0
% 1.91/1.23  #Define  : 0
% 1.91/1.23  #Split   : 2
% 1.91/1.23  #Chain   : 0
% 1.91/1.23  #Close   : 0
% 1.91/1.23  
% 1.91/1.23  Ordering : KBO
% 1.91/1.23  
% 1.91/1.23  Simplification rules
% 1.91/1.23  ----------------------
% 1.91/1.23  #Subsume      : 2
% 1.91/1.23  #Demod        : 4
% 1.91/1.23  #Tautology    : 9
% 1.91/1.23  #SimpNegUnit  : 2
% 1.91/1.23  #BackRed      : 0
% 1.91/1.23  
% 1.91/1.23  #Partial instantiations: 0
% 1.91/1.23  #Strategies tried      : 1
% 1.91/1.23  
% 1.91/1.23  Timing (in seconds)
% 1.91/1.23  ----------------------
% 1.91/1.23  Preprocessing        : 0.32
% 1.91/1.23  Parsing              : 0.16
% 1.91/1.23  CNF conversion       : 0.02
% 1.91/1.23  Main loop            : 0.11
% 1.91/1.23  Inferencing          : 0.03
% 1.91/1.23  Reduction            : 0.03
% 1.91/1.23  Demodulation         : 0.02
% 1.91/1.23  BG Simplification    : 0.01
% 1.91/1.23  Subsumption          : 0.02
% 1.91/1.23  Abstraction          : 0.01
% 1.91/1.23  MUC search           : 0.00
% 1.91/1.23  Cooper               : 0.00
% 1.91/1.23  Total                : 0.45
% 1.91/1.23  Index Insertion      : 0.00
% 1.91/1.23  Index Deletion       : 0.00
% 1.91/1.23  Index Matching       : 0.00
% 1.91/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

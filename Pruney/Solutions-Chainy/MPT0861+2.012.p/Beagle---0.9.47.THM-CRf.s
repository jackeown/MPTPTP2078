%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:09:02 EST 2020

% Result     : Theorem 1.87s
% Output     : CNFRefutation 1.87s
% Verified   : 
% Statistics : Number of formulae       :   51 (  89 expanded)
%              Number of leaves         :   22 (  40 expanded)
%              Depth                    :    6
%              Number of atoms          :   49 ( 139 expanded)
%              Number of equality atoms :   38 ( 108 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k3_relat_1 > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k3_relat_1,type,(
    k3_relat_1: $i > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_mcart_1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k1_tarski(A),k2_tarski(B,C)) = k2_tarski(k4_tarski(A,B),k4_tarski(A,C))
      & k2_zfmisc_1(k2_tarski(A,B),k1_tarski(C)) = k2_tarski(k4_tarski(A,C),k4_tarski(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_50,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_mcart_1)).

tff(c_38,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_62,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_26,plain,(
    ! [A_12,B_13,C_14] : k2_zfmisc_1(k2_tarski(A_12,B_13),k1_tarski(C_14)) = k2_tarski(k4_tarski(A_12,C_14),k4_tarski(B_13,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_36,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_41,plain,(
    r2_hidden('#skF_3',k2_tarski(k4_tarski('#skF_4','#skF_6'),k4_tarski('#skF_5','#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_36])).

tff(c_115,plain,(
    ! [D_34,B_35,A_36] :
      ( D_34 = B_35
      | D_34 = A_36
      | ~ r2_hidden(D_34,k2_tarski(A_36,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_128,plain,
    ( k4_tarski('#skF_5','#skF_6') = '#skF_3'
    | k4_tarski('#skF_4','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_41,c_115])).

tff(c_133,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_128])).

tff(c_34,plain,(
    ! [A_18,B_19] : k2_mcart_1(k4_tarski(A_18,B_19)) = B_19 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_145,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_133,c_34])).

tff(c_149,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_145])).

tff(c_150,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_128])).

tff(c_163,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_34])).

tff(c_167,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_163])).

tff(c_168,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_169,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_40,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_170,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_176,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_170])).

tff(c_177,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_236,plain,(
    ! [D_43,B_44,A_45] :
      ( D_43 = B_44
      | D_43 = A_45
      | ~ r2_hidden(D_43,k2_tarski(A_45,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_249,plain,
    ( k4_tarski('#skF_5','#skF_6') = '#skF_3'
    | k4_tarski('#skF_4','#skF_6') = '#skF_3' ),
    inference(resolution,[status(thm)],[c_41,c_236])).

tff(c_254,plain,(
    k4_tarski('#skF_4','#skF_6') = '#skF_3' ),
    inference(splitLeft,[status(thm)],[c_249])).

tff(c_32,plain,(
    ! [A_18,B_19] : k1_mcart_1(k4_tarski(A_18,B_19)) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_263,plain,(
    k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_254,c_32])).

tff(c_270,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_177,c_263])).

tff(c_271,plain,(
    k4_tarski('#skF_5','#skF_6') = '#skF_3' ),
    inference(splitRight,[status(thm)],[c_249])).

tff(c_281,plain,(
    k1_mcart_1('#skF_3') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_271,c_32])).

tff(c_288,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_168,c_281])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:48:04 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.87/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.20  
% 1.87/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.20  %$ r2_hidden > k2_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k3_relat_1 > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 1.87/1.20  
% 1.87/1.20  %Foreground sorts:
% 1.87/1.20  
% 1.87/1.20  
% 1.87/1.20  %Background operators:
% 1.87/1.20  
% 1.87/1.20  
% 1.87/1.20  %Foreground operators:
% 1.87/1.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.87/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.87/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.87/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.87/1.20  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 1.87/1.20  tff(k3_relat_1, type, k3_relat_1: $i > $i).
% 1.87/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.87/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.87/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.87/1.20  tff('#skF_6', type, '#skF_6': $i).
% 1.87/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.87/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.87/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.87/1.20  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.87/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.87/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.87/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.87/1.20  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.87/1.20  
% 1.87/1.21  tff(f_59, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_mcart_1)).
% 1.87/1.21  tff(f_42, axiom, (![A, B, C]: ((k2_zfmisc_1(k1_tarski(A), k2_tarski(B, C)) = k2_tarski(k4_tarski(A, B), k4_tarski(A, C))) & (k2_zfmisc_1(k2_tarski(A, B), k1_tarski(C)) = k2_tarski(k4_tarski(A, C), k4_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_zfmisc_1)).
% 1.87/1.21  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.87/1.21  tff(f_50, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_mcart_1)).
% 1.87/1.21  tff(c_38, plain, (k1_mcart_1('#skF_3')!='#skF_5' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.87/1.21  tff(c_62, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitLeft, [status(thm)], [c_38])).
% 1.87/1.21  tff(c_26, plain, (![A_12, B_13, C_14]: (k2_zfmisc_1(k2_tarski(A_12, B_13), k1_tarski(C_14))=k2_tarski(k4_tarski(A_12, C_14), k4_tarski(B_13, C_14)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.87/1.21  tff(c_36, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.87/1.21  tff(c_41, plain, (r2_hidden('#skF_3', k2_tarski(k4_tarski('#skF_4', '#skF_6'), k4_tarski('#skF_5', '#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_26, c_36])).
% 1.87/1.21  tff(c_115, plain, (![D_34, B_35, A_36]: (D_34=B_35 | D_34=A_36 | ~r2_hidden(D_34, k2_tarski(A_36, B_35)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.87/1.21  tff(c_128, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_3' | k4_tarski('#skF_4', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_41, c_115])).
% 1.87/1.21  tff(c_133, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_128])).
% 1.87/1.21  tff(c_34, plain, (![A_18, B_19]: (k2_mcart_1(k4_tarski(A_18, B_19))=B_19)), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.21  tff(c_145, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_133, c_34])).
% 1.87/1.21  tff(c_149, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_145])).
% 1.87/1.21  tff(c_150, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_3'), inference(splitRight, [status(thm)], [c_128])).
% 1.87/1.21  tff(c_163, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_150, c_34])).
% 1.87/1.21  tff(c_167, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_163])).
% 1.87/1.21  tff(c_168, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_38])).
% 1.87/1.21  tff(c_169, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_38])).
% 1.87/1.21  tff(c_40, plain, (k1_mcart_1('#skF_3')!='#skF_4' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.87/1.21  tff(c_170, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitLeft, [status(thm)], [c_40])).
% 1.87/1.21  tff(c_176, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_169, c_170])).
% 1.87/1.21  tff(c_177, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitRight, [status(thm)], [c_40])).
% 1.87/1.21  tff(c_236, plain, (![D_43, B_44, A_45]: (D_43=B_44 | D_43=A_45 | ~r2_hidden(D_43, k2_tarski(A_45, B_44)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.87/1.21  tff(c_249, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_3' | k4_tarski('#skF_4', '#skF_6')='#skF_3'), inference(resolution, [status(thm)], [c_41, c_236])).
% 1.87/1.21  tff(c_254, plain, (k4_tarski('#skF_4', '#skF_6')='#skF_3'), inference(splitLeft, [status(thm)], [c_249])).
% 1.87/1.21  tff(c_32, plain, (![A_18, B_19]: (k1_mcart_1(k4_tarski(A_18, B_19))=A_18)), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.87/1.21  tff(c_263, plain, (k1_mcart_1('#skF_3')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_254, c_32])).
% 1.87/1.21  tff(c_270, plain, $false, inference(negUnitSimplification, [status(thm)], [c_177, c_263])).
% 1.87/1.21  tff(c_271, plain, (k4_tarski('#skF_5', '#skF_6')='#skF_3'), inference(splitRight, [status(thm)], [c_249])).
% 1.87/1.21  tff(c_281, plain, (k1_mcart_1('#skF_3')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_271, c_32])).
% 1.87/1.21  tff(c_288, plain, $false, inference(negUnitSimplification, [status(thm)], [c_168, c_281])).
% 1.87/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.87/1.21  
% 1.87/1.21  Inference rules
% 1.87/1.21  ----------------------
% 1.87/1.21  #Ref     : 0
% 1.87/1.21  #Sup     : 60
% 1.87/1.21  #Fact    : 0
% 1.87/1.21  #Define  : 0
% 1.87/1.21  #Split   : 4
% 1.87/1.21  #Chain   : 0
% 1.87/1.21  #Close   : 0
% 1.87/1.21  
% 1.87/1.21  Ordering : KBO
% 1.87/1.21  
% 1.87/1.21  Simplification rules
% 1.87/1.21  ----------------------
% 1.87/1.21  #Subsume      : 1
% 1.87/1.21  #Demod        : 15
% 1.87/1.21  #Tautology    : 41
% 1.87/1.21  #SimpNegUnit  : 4
% 1.87/1.21  #BackRed      : 4
% 1.87/1.21  
% 1.87/1.21  #Partial instantiations: 0
% 1.87/1.21  #Strategies tried      : 1
% 1.87/1.21  
% 1.87/1.21  Timing (in seconds)
% 1.87/1.21  ----------------------
% 2.01/1.21  Preprocessing        : 0.30
% 2.01/1.21  Parsing              : 0.16
% 2.01/1.21  CNF conversion       : 0.02
% 2.01/1.21  Main loop            : 0.15
% 2.01/1.21  Inferencing          : 0.05
% 2.01/1.21  Reduction            : 0.05
% 2.01/1.21  Demodulation         : 0.04
% 2.01/1.21  BG Simplification    : 0.01
% 2.01/1.21  Subsumption          : 0.02
% 2.01/1.21  Abstraction          : 0.01
% 2.01/1.21  MUC search           : 0.00
% 2.01/1.21  Cooper               : 0.00
% 2.01/1.21  Total                : 0.48
% 2.01/1.21  Index Insertion      : 0.00
% 2.01/1.21  Index Deletion       : 0.00
% 2.01/1.21  Index Matching       : 0.00
% 2.01/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

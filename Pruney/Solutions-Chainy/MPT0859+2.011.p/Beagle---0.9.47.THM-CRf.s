%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:08:59 EST 2020

% Result     : Theorem 2.71s
% Output     : CNFRefutation 2.76s
% Verified   : 
% Statistics : Number of formulae       :   54 (  92 expanded)
%              Number of leaves         :   22 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   63 ( 151 expanded)
%              Number of equality atoms :   31 (  75 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

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

tff(k1_mcart_1,type,(
    k1_mcart_1: $i > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_mcart_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ~ ( r2_hidden(A,k2_zfmisc_1(B,C))
        & ! [D,E] : k4_tarski(D,E) != A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l139_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k1_mcart_1(k4_tarski(A,B)) = A
      & k2_mcart_1(k4_tarski(A,B)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_mcart_1)).

tff(f_47,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t106_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_34,plain,
    ( k1_mcart_1('#skF_5') != '#skF_7'
    | ~ r2_hidden(k2_mcart_1('#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_57,plain,(
    ~ r2_hidden(k2_mcart_1('#skF_5'),'#skF_8') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_32,plain,(
    r2_hidden('#skF_5',k2_zfmisc_1(k2_tarski('#skF_6','#skF_7'),'#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_82,plain,(
    ! [A_47,B_48,C_49] :
      ( k4_tarski('#skF_3'(A_47,B_48,C_49),'#skF_4'(A_47,B_48,C_49)) = A_47
      | ~ r2_hidden(A_47,k2_zfmisc_1(B_48,C_49)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_28,plain,(
    ! [A_16,B_17] : k1_mcart_1(k4_tarski(A_16,B_17)) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_107,plain,(
    ! [A_53,B_54,C_55] :
      ( k1_mcart_1(A_53) = '#skF_3'(A_53,B_54,C_55)
      | ~ r2_hidden(A_53,k2_zfmisc_1(B_54,C_55)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_28])).

tff(c_116,plain,(
    '#skF_3'('#skF_5',k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_mcart_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_107])).

tff(c_20,plain,(
    ! [A_7,B_8,C_9] :
      ( k4_tarski('#skF_3'(A_7,B_8,C_9),'#skF_4'(A_7,B_8,C_9)) = A_7
      | ~ r2_hidden(A_7,k2_zfmisc_1(B_8,C_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_120,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),'#skF_4'('#skF_5',k2_tarski('#skF_6','#skF_7'),'#skF_8')) = '#skF_5'
    | ~ r2_hidden('#skF_5',k2_zfmisc_1(k2_tarski('#skF_6','#skF_7'),'#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_116,c_20])).

tff(c_124,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),'#skF_4'('#skF_5',k2_tarski('#skF_6','#skF_7'),'#skF_8')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_120])).

tff(c_30,plain,(
    ! [A_16,B_17] : k2_mcart_1(k4_tarski(A_16,B_17)) = B_17 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_141,plain,(
    '#skF_4'('#skF_5',k2_tarski('#skF_6','#skF_7'),'#skF_8') = k2_mcart_1('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_30])).

tff(c_146,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),k2_mcart_1('#skF_5')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_124])).

tff(c_24,plain,(
    ! [B_13,D_15,A_12,C_14] :
      ( r2_hidden(B_13,D_15)
      | ~ r2_hidden(k4_tarski(A_12,B_13),k2_zfmisc_1(C_14,D_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_710,plain,(
    ! [D_634,C_635] :
      ( r2_hidden(k2_mcart_1('#skF_5'),D_634)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(C_635,D_634)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_146,c_24])).

tff(c_713,plain,(
    r2_hidden(k2_mcart_1('#skF_5'),'#skF_8') ),
    inference(resolution,[status(thm)],[c_32,c_710])).

tff(c_717,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_57,c_713])).

tff(c_719,plain,(
    r2_hidden(k2_mcart_1('#skF_5'),'#skF_8') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36,plain,
    ( k1_mcart_1('#skF_5') != '#skF_6'
    | ~ r2_hidden(k2_mcart_1('#skF_5'),'#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_721,plain,(
    k1_mcart_1('#skF_5') != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_719,c_36])).

tff(c_718,plain,(
    k1_mcart_1('#skF_5') != '#skF_7' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_746,plain,(
    ! [A_677,B_678,C_679] :
      ( k4_tarski('#skF_3'(A_677,B_678,C_679),'#skF_4'(A_677,B_678,C_679)) = A_677
      | ~ r2_hidden(A_677,k2_zfmisc_1(B_678,C_679)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_770,plain,(
    ! [A_680,B_681,C_682] :
      ( k1_mcart_1(A_680) = '#skF_3'(A_680,B_681,C_682)
      | ~ r2_hidden(A_680,k2_zfmisc_1(B_681,C_682)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_746,c_28])).

tff(c_779,plain,(
    '#skF_3'('#skF_5',k2_tarski('#skF_6','#skF_7'),'#skF_8') = k1_mcart_1('#skF_5') ),
    inference(resolution,[status(thm)],[c_32,c_770])).

tff(c_783,plain,
    ( k4_tarski(k1_mcart_1('#skF_5'),'#skF_4'('#skF_5',k2_tarski('#skF_6','#skF_7'),'#skF_8')) = '#skF_5'
    | ~ r2_hidden('#skF_5',k2_zfmisc_1(k2_tarski('#skF_6','#skF_7'),'#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_779,c_20])).

tff(c_787,plain,(
    k4_tarski(k1_mcart_1('#skF_5'),'#skF_4'('#skF_5',k2_tarski('#skF_6','#skF_7'),'#skF_8')) = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_783])).

tff(c_26,plain,(
    ! [A_12,C_14,B_13,D_15] :
      ( r2_hidden(A_12,C_14)
      | ~ r2_hidden(k4_tarski(A_12,B_13),k2_zfmisc_1(C_14,D_15)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_841,plain,(
    ! [C_683,D_684] :
      ( r2_hidden(k1_mcart_1('#skF_5'),C_683)
      | ~ r2_hidden('#skF_5',k2_zfmisc_1(C_683,D_684)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_787,c_26])).

tff(c_844,plain,(
    r2_hidden(k1_mcart_1('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(resolution,[status(thm)],[c_32,c_841])).

tff(c_2,plain,(
    ! [D_6,B_2,A_1] :
      ( D_6 = B_2
      | D_6 = A_1
      | ~ r2_hidden(D_6,k2_tarski(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_847,plain,
    ( k1_mcart_1('#skF_5') = '#skF_7'
    | k1_mcart_1('#skF_5') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_844,c_2])).

tff(c_851,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_721,c_718,c_847])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:12:57 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.71/1.46  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.46  
% 2.71/1.46  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.71/1.46  %$ r2_hidden > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_mcart_1 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_8 > #skF_3
% 2.71/1.46  
% 2.71/1.46  %Foreground sorts:
% 2.71/1.46  
% 2.71/1.46  
% 2.71/1.46  %Background operators:
% 2.71/1.46  
% 2.71/1.46  
% 2.71/1.46  %Foreground operators:
% 2.71/1.46  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.71/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.71/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.71/1.46  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.71/1.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.71/1.46  tff('#skF_7', type, '#skF_7': $i).
% 2.71/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.71/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.71/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.71/1.46  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.71/1.46  tff('#skF_8', type, '#skF_8': $i).
% 2.71/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.71/1.46  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 2.71/1.46  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.71/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.71/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.71/1.46  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 2.71/1.46  
% 2.76/1.47  tff(f_60, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_mcart_1)).
% 2.76/1.47  tff(f_41, axiom, (![A, B, C]: ~(r2_hidden(A, k2_zfmisc_1(B, C)) & (![D, E]: ~(k4_tarski(D, E) = A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l139_zfmisc_1)).
% 2.76/1.47  tff(f_51, axiom, (![A, B]: ((k1_mcart_1(k4_tarski(A, B)) = A) & (k2_mcart_1(k4_tarski(A, B)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_mcart_1)).
% 2.76/1.47  tff(f_47, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t106_zfmisc_1)).
% 2.76/1.47  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.76/1.47  tff(c_34, plain, (k1_mcart_1('#skF_5')!='#skF_7' | ~r2_hidden(k2_mcart_1('#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.76/1.47  tff(c_57, plain, (~r2_hidden(k2_mcart_1('#skF_5'), '#skF_8')), inference(splitLeft, [status(thm)], [c_34])).
% 2.76/1.47  tff(c_32, plain, (r2_hidden('#skF_5', k2_zfmisc_1(k2_tarski('#skF_6', '#skF_7'), '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.76/1.47  tff(c_82, plain, (![A_47, B_48, C_49]: (k4_tarski('#skF_3'(A_47, B_48, C_49), '#skF_4'(A_47, B_48, C_49))=A_47 | ~r2_hidden(A_47, k2_zfmisc_1(B_48, C_49)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.76/1.47  tff(c_28, plain, (![A_16, B_17]: (k1_mcart_1(k4_tarski(A_16, B_17))=A_16)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.76/1.47  tff(c_107, plain, (![A_53, B_54, C_55]: (k1_mcart_1(A_53)='#skF_3'(A_53, B_54, C_55) | ~r2_hidden(A_53, k2_zfmisc_1(B_54, C_55)))), inference(superposition, [status(thm), theory('equality')], [c_82, c_28])).
% 2.76/1.47  tff(c_116, plain, ('#skF_3'('#skF_5', k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_mcart_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_107])).
% 2.76/1.48  tff(c_20, plain, (![A_7, B_8, C_9]: (k4_tarski('#skF_3'(A_7, B_8, C_9), '#skF_4'(A_7, B_8, C_9))=A_7 | ~r2_hidden(A_7, k2_zfmisc_1(B_8, C_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.76/1.48  tff(c_120, plain, (k4_tarski(k1_mcart_1('#skF_5'), '#skF_4'('#skF_5', k2_tarski('#skF_6', '#skF_7'), '#skF_8'))='#skF_5' | ~r2_hidden('#skF_5', k2_zfmisc_1(k2_tarski('#skF_6', '#skF_7'), '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_116, c_20])).
% 2.76/1.48  tff(c_124, plain, (k4_tarski(k1_mcart_1('#skF_5'), '#skF_4'('#skF_5', k2_tarski('#skF_6', '#skF_7'), '#skF_8'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_120])).
% 2.76/1.48  tff(c_30, plain, (![A_16, B_17]: (k2_mcart_1(k4_tarski(A_16, B_17))=B_17)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.76/1.48  tff(c_141, plain, ('#skF_4'('#skF_5', k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k2_mcart_1('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_124, c_30])).
% 2.76/1.48  tff(c_146, plain, (k4_tarski(k1_mcart_1('#skF_5'), k2_mcart_1('#skF_5'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_141, c_124])).
% 2.76/1.48  tff(c_24, plain, (![B_13, D_15, A_12, C_14]: (r2_hidden(B_13, D_15) | ~r2_hidden(k4_tarski(A_12, B_13), k2_zfmisc_1(C_14, D_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.76/1.48  tff(c_710, plain, (![D_634, C_635]: (r2_hidden(k2_mcart_1('#skF_5'), D_634) | ~r2_hidden('#skF_5', k2_zfmisc_1(C_635, D_634)))), inference(superposition, [status(thm), theory('equality')], [c_146, c_24])).
% 2.76/1.48  tff(c_713, plain, (r2_hidden(k2_mcart_1('#skF_5'), '#skF_8')), inference(resolution, [status(thm)], [c_32, c_710])).
% 2.76/1.48  tff(c_717, plain, $false, inference(negUnitSimplification, [status(thm)], [c_57, c_713])).
% 2.76/1.48  tff(c_719, plain, (r2_hidden(k2_mcart_1('#skF_5'), '#skF_8')), inference(splitRight, [status(thm)], [c_34])).
% 2.76/1.48  tff(c_36, plain, (k1_mcart_1('#skF_5')!='#skF_6' | ~r2_hidden(k2_mcart_1('#skF_5'), '#skF_8')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.76/1.48  tff(c_721, plain, (k1_mcart_1('#skF_5')!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_719, c_36])).
% 2.76/1.48  tff(c_718, plain, (k1_mcart_1('#skF_5')!='#skF_7'), inference(splitRight, [status(thm)], [c_34])).
% 2.76/1.48  tff(c_746, plain, (![A_677, B_678, C_679]: (k4_tarski('#skF_3'(A_677, B_678, C_679), '#skF_4'(A_677, B_678, C_679))=A_677 | ~r2_hidden(A_677, k2_zfmisc_1(B_678, C_679)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.76/1.48  tff(c_770, plain, (![A_680, B_681, C_682]: (k1_mcart_1(A_680)='#skF_3'(A_680, B_681, C_682) | ~r2_hidden(A_680, k2_zfmisc_1(B_681, C_682)))), inference(superposition, [status(thm), theory('equality')], [c_746, c_28])).
% 2.76/1.48  tff(c_779, plain, ('#skF_3'('#skF_5', k2_tarski('#skF_6', '#skF_7'), '#skF_8')=k1_mcart_1('#skF_5')), inference(resolution, [status(thm)], [c_32, c_770])).
% 2.76/1.48  tff(c_783, plain, (k4_tarski(k1_mcart_1('#skF_5'), '#skF_4'('#skF_5', k2_tarski('#skF_6', '#skF_7'), '#skF_8'))='#skF_5' | ~r2_hidden('#skF_5', k2_zfmisc_1(k2_tarski('#skF_6', '#skF_7'), '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_779, c_20])).
% 2.76/1.48  tff(c_787, plain, (k4_tarski(k1_mcart_1('#skF_5'), '#skF_4'('#skF_5', k2_tarski('#skF_6', '#skF_7'), '#skF_8'))='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_32, c_783])).
% 2.76/1.48  tff(c_26, plain, (![A_12, C_14, B_13, D_15]: (r2_hidden(A_12, C_14) | ~r2_hidden(k4_tarski(A_12, B_13), k2_zfmisc_1(C_14, D_15)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.76/1.48  tff(c_841, plain, (![C_683, D_684]: (r2_hidden(k1_mcart_1('#skF_5'), C_683) | ~r2_hidden('#skF_5', k2_zfmisc_1(C_683, D_684)))), inference(superposition, [status(thm), theory('equality')], [c_787, c_26])).
% 2.76/1.48  tff(c_844, plain, (r2_hidden(k1_mcart_1('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(resolution, [status(thm)], [c_32, c_841])).
% 2.76/1.48  tff(c_2, plain, (![D_6, B_2, A_1]: (D_6=B_2 | D_6=A_1 | ~r2_hidden(D_6, k2_tarski(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.76/1.48  tff(c_847, plain, (k1_mcart_1('#skF_5')='#skF_7' | k1_mcart_1('#skF_5')='#skF_6'), inference(resolution, [status(thm)], [c_844, c_2])).
% 2.76/1.48  tff(c_851, plain, $false, inference(negUnitSimplification, [status(thm)], [c_721, c_718, c_847])).
% 2.76/1.48  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.76/1.48  
% 2.76/1.48  Inference rules
% 2.76/1.48  ----------------------
% 2.76/1.48  #Ref     : 0
% 2.76/1.48  #Sup     : 139
% 2.76/1.48  #Fact    : 2
% 2.76/1.48  #Define  : 0
% 2.76/1.48  #Split   : 3
% 2.76/1.48  #Chain   : 0
% 2.76/1.48  #Close   : 0
% 2.76/1.48  
% 2.76/1.48  Ordering : KBO
% 2.76/1.48  
% 2.76/1.48  Simplification rules
% 2.76/1.48  ----------------------
% 2.76/1.48  #Subsume      : 7
% 2.76/1.48  #Demod        : 24
% 2.76/1.48  #Tautology    : 55
% 2.76/1.48  #SimpNegUnit  : 2
% 2.76/1.48  #BackRed      : 6
% 2.76/1.48  
% 2.76/1.48  #Partial instantiations: 364
% 2.76/1.48  #Strategies tried      : 1
% 2.76/1.48  
% 2.76/1.48  Timing (in seconds)
% 2.76/1.48  ----------------------
% 2.76/1.48  Preprocessing        : 0.30
% 2.76/1.48  Parsing              : 0.16
% 2.76/1.48  CNF conversion       : 0.02
% 2.76/1.48  Main loop            : 0.36
% 2.76/1.48  Inferencing          : 0.18
% 2.76/1.48  Reduction            : 0.09
% 2.76/1.48  Demodulation         : 0.06
% 2.76/1.48  BG Simplification    : 0.02
% 2.76/1.48  Subsumption          : 0.05
% 2.76/1.48  Abstraction          : 0.02
% 2.76/1.48  MUC search           : 0.00
% 2.76/1.48  Cooper               : 0.00
% 2.76/1.48  Total                : 0.69
% 2.76/1.48  Index Insertion      : 0.00
% 2.76/1.48  Index Deletion       : 0.00
% 2.76/1.48  Index Matching       : 0.00
% 2.76/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------

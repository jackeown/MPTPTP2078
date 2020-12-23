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
% DateTime   : Thu Dec  3 10:09:02 EST 2020

% Result     : Theorem 1.74s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   39 (  51 expanded)
%              Number of leaves         :   22 (  29 expanded)
%              Depth                    :    4
%              Number of atoms          :   40 (  76 expanded)
%              Number of equality atoms :   27 (  54 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4

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

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),k1_tarski(D)))
       => ( ( k1_mcart_1(A) = B
            | k1_mcart_1(A) = C )
          & k2_mcart_1(A) = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_mcart_1)).

tff(f_50,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(A,k2_zfmisc_1(k2_tarski(B,C),D))
     => ( ( k1_mcart_1(A) = B
          | k1_mcart_1(A) = C )
        & r2_hidden(k2_mcart_1(A),D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_mcart_1)).

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

tff(c_36,plain,
    ( k1_mcart_1('#skF_3') != '#skF_4'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_56,plain,(
    k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_32,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_104,plain,(
    ! [A_41,D_42,B_43,C_44] :
      ( r2_hidden(k2_mcart_1(A_41),D_42)
      | ~ r2_hidden(A_41,k2_zfmisc_1(k2_tarski(B_43,C_44),D_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_110,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_32,c_104])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    ! [D_29,B_30,A_31] :
      ( D_29 = B_30
      | D_29 = A_31
      | ~ r2_hidden(D_29,k2_tarski(A_31,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_75,plain,(
    ! [D_29,A_7] :
      ( D_29 = A_7
      | D_29 = A_7
      | ~ r2_hidden(D_29,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_66])).

tff(c_113,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(resolution,[status(thm)],[c_110,c_75])).

tff(c_117,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_113])).

tff(c_118,plain,(
    k1_mcart_1('#skF_3') != '#skF_4' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_119,plain,(
    k2_mcart_1('#skF_3') = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_34,plain,
    ( k1_mcart_1('#skF_3') != '#skF_5'
    | k2_mcart_1('#skF_3') != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_125,plain,(
    k1_mcart_1('#skF_3') != '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_119,c_34])).

tff(c_181,plain,(
    ! [A_63,C_64,B_65,D_66] :
      ( k1_mcart_1(A_63) = C_64
      | k1_mcart_1(A_63) = B_65
      | ~ r2_hidden(A_63,k2_zfmisc_1(k2_tarski(B_65,C_64),D_66)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_184,plain,
    ( k1_mcart_1('#skF_3') = '#skF_5'
    | k1_mcart_1('#skF_3') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_32,c_181])).

tff(c_191,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_118,c_125,c_184])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.33  % Computer   : n022.cluster.edu
% 0.14/0.33  % Model      : x86_64 x86_64
% 0.14/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.33  % Memory     : 8042.1875MB
% 0.14/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.33  % CPULimit   : 60
% 0.14/0.33  % DateTime   : Tue Dec  1 18:37:41 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.74/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.16  
% 1.74/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.74/1.16  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_6 > #skF_3 > #skF_2 > #skF_4
% 1.74/1.16  
% 1.74/1.16  %Foreground sorts:
% 1.74/1.16  
% 1.74/1.16  
% 1.74/1.16  %Background operators:
% 1.74/1.16  
% 1.74/1.16  
% 1.74/1.16  %Foreground operators:
% 1.74/1.16  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.74/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.74/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.74/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.74/1.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.74/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.74/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.74/1.16  tff('#skF_5', type, '#skF_5': $i).
% 1.74/1.16  tff('#skF_6', type, '#skF_6': $i).
% 1.74/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.74/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.74/1.16  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.74/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.74/1.16  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.74/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.74/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.74/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.74/1.16  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.74/1.16  
% 1.93/1.17  tff(f_59, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), k1_tarski(D))) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & (k2_mcart_1(A) = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_mcart_1)).
% 1.93/1.17  tff(f_50, axiom, (![A, B, C, D]: (r2_hidden(A, k2_zfmisc_1(k2_tarski(B, C), D)) => (((k1_mcart_1(A) = B) | (k1_mcart_1(A) = C)) & r2_hidden(k2_mcart_1(A), D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_mcart_1)).
% 1.93/1.17  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.93/1.17  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.93/1.17  tff(c_36, plain, (k1_mcart_1('#skF_3')!='#skF_4' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.93/1.17  tff(c_56, plain, (k2_mcart_1('#skF_3')!='#skF_6'), inference(splitLeft, [status(thm)], [c_36])).
% 1.93/1.17  tff(c_32, plain, (r2_hidden('#skF_3', k2_zfmisc_1(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_6')))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.93/1.17  tff(c_104, plain, (![A_41, D_42, B_43, C_44]: (r2_hidden(k2_mcart_1(A_41), D_42) | ~r2_hidden(A_41, k2_zfmisc_1(k2_tarski(B_43, C_44), D_42)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.17  tff(c_110, plain, (r2_hidden(k2_mcart_1('#skF_3'), k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_32, c_104])).
% 1.93/1.17  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.93/1.17  tff(c_66, plain, (![D_29, B_30, A_31]: (D_29=B_30 | D_29=A_31 | ~r2_hidden(D_29, k2_tarski(A_31, B_30)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.93/1.17  tff(c_75, plain, (![D_29, A_7]: (D_29=A_7 | D_29=A_7 | ~r2_hidden(D_29, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_66])).
% 1.93/1.17  tff(c_113, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(resolution, [status(thm)], [c_110, c_75])).
% 1.93/1.17  tff(c_117, plain, $false, inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_113])).
% 1.93/1.17  tff(c_118, plain, (k1_mcart_1('#skF_3')!='#skF_4'), inference(splitRight, [status(thm)], [c_36])).
% 1.93/1.17  tff(c_119, plain, (k2_mcart_1('#skF_3')='#skF_6'), inference(splitRight, [status(thm)], [c_36])).
% 1.93/1.17  tff(c_34, plain, (k1_mcart_1('#skF_3')!='#skF_5' | k2_mcart_1('#skF_3')!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.93/1.17  tff(c_125, plain, (k1_mcart_1('#skF_3')!='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_119, c_34])).
% 1.93/1.17  tff(c_181, plain, (![A_63, C_64, B_65, D_66]: (k1_mcart_1(A_63)=C_64 | k1_mcart_1(A_63)=B_65 | ~r2_hidden(A_63, k2_zfmisc_1(k2_tarski(B_65, C_64), D_66)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.93/1.17  tff(c_184, plain, (k1_mcart_1('#skF_3')='#skF_5' | k1_mcart_1('#skF_3')='#skF_4'), inference(resolution, [status(thm)], [c_32, c_181])).
% 1.93/1.17  tff(c_191, plain, $false, inference(negUnitSimplification, [status(thm)], [c_118, c_125, c_184])).
% 1.93/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.93/1.17  
% 1.93/1.17  Inference rules
% 1.93/1.17  ----------------------
% 1.93/1.17  #Ref     : 0
% 1.93/1.17  #Sup     : 33
% 1.93/1.17  #Fact    : 0
% 1.93/1.17  #Define  : 0
% 1.93/1.17  #Split   : 1
% 1.93/1.17  #Chain   : 0
% 1.93/1.17  #Close   : 0
% 1.93/1.17  
% 1.93/1.17  Ordering : KBO
% 1.93/1.17  
% 1.93/1.17  Simplification rules
% 1.93/1.17  ----------------------
% 1.93/1.17  #Subsume      : 1
% 1.93/1.17  #Demod        : 4
% 1.93/1.17  #Tautology    : 24
% 1.93/1.17  #SimpNegUnit  : 2
% 1.93/1.17  #BackRed      : 0
% 1.93/1.17  
% 1.93/1.17  #Partial instantiations: 0
% 1.93/1.17  #Strategies tried      : 1
% 1.93/1.17  
% 1.93/1.17  Timing (in seconds)
% 1.93/1.17  ----------------------
% 1.93/1.17  Preprocessing        : 0.29
% 1.93/1.17  Parsing              : 0.15
% 1.93/1.17  CNF conversion       : 0.02
% 1.93/1.17  Main loop            : 0.14
% 1.93/1.17  Inferencing          : 0.05
% 1.93/1.17  Reduction            : 0.04
% 1.93/1.17  Demodulation         : 0.03
% 1.93/1.17  BG Simplification    : 0.01
% 1.93/1.17  Subsumption          : 0.02
% 1.93/1.17  Abstraction          : 0.01
% 1.93/1.17  MUC search           : 0.00
% 1.93/1.17  Cooper               : 0.00
% 1.93/1.17  Total                : 0.45
% 1.93/1.17  Index Insertion      : 0.00
% 1.93/1.17  Index Deletion       : 0.00
% 1.93/1.17  Index Matching       : 0.00
% 1.93/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------

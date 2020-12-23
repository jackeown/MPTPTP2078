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
% DateTime   : Thu Dec  3 10:08:54 EST 2020

% Result     : Theorem 1.76s
% Output     : CNFRefutation 1.76s
% Verified   : 
% Statistics : Number of formulae       :   37 (  46 expanded)
%              Number of leaves         :   21 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   35 (  56 expanded)
%              Number of equality atoms :   16 (  23 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k2_zfmisc_1(B,k1_tarski(C)))
       => ( r2_hidden(k1_mcart_1(A),B)
          & k2_mcart_1(A) = C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_mcart_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k2_zfmisc_1(B,C))
     => ( r2_hidden(k1_mcart_1(A),B)
        & r2_hidden(k2_mcart_1(A),C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_mcart_1)).

tff(f_36,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_38,axiom,(
    ! [A] : k1_enumset1(A,A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t76_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_30,plain,
    ( k2_mcart_1('#skF_3') != '#skF_5'
    | ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_44,plain,(
    ~ r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_32,plain,(
    r2_hidden('#skF_3',k2_zfmisc_1('#skF_4',k1_tarski('#skF_5'))) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_99,plain,(
    ! [A_30,B_31,C_32] :
      ( r2_hidden(k1_mcart_1(A_30),B_31)
      | ~ r2_hidden(A_30,k2_zfmisc_1(B_31,C_32)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_101,plain,(
    r2_hidden(k1_mcart_1('#skF_3'),'#skF_4') ),
    inference(resolution,[status(thm)],[c_32,c_99])).

tff(c_105,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_44,c_101])).

tff(c_106,plain,(
    k2_mcart_1('#skF_3') != '#skF_5' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_167,plain,(
    ! [A_45,C_46,B_47] :
      ( r2_hidden(k2_mcart_1(A_45),C_46)
      | ~ r2_hidden(A_45,k2_zfmisc_1(B_47,C_46)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_170,plain,(
    r2_hidden(k2_mcart_1('#skF_3'),k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_32,c_167])).

tff(c_108,plain,(
    ! [A_33,B_34] : k1_enumset1(A_33,A_33,B_34) = k2_tarski(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_22,plain,(
    ! [A_9] : k1_enumset1(A_9,A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_115,plain,(
    ! [B_34] : k2_tarski(B_34,B_34) = k1_tarski(B_34) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_22])).

tff(c_140,plain,(
    ! [D_37,B_38,A_39] :
      ( D_37 = B_38
      | D_37 = A_39
      | ~ r2_hidden(D_37,k2_tarski(A_39,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_143,plain,(
    ! [D_37,B_34] :
      ( D_37 = B_34
      | D_37 = B_34
      | ~ r2_hidden(D_37,k1_tarski(B_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_140])).

tff(c_182,plain,(
    k2_mcart_1('#skF_3') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_170,c_143])).

tff(c_186,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_106,c_106,c_182])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 15:12:35 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.76/1.18  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.18  
% 1.76/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.18  %$ r2_hidden > k3_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_tarski > #nlpp > k2_mcart_1 > k1_tarski > k1_mcart_1 > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.76/1.18  
% 1.76/1.18  %Foreground sorts:
% 1.76/1.18  
% 1.76/1.18  
% 1.76/1.18  %Background operators:
% 1.76/1.18  
% 1.76/1.18  
% 1.76/1.18  %Foreground operators:
% 1.76/1.18  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.76/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.76/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.76/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.76/1.18  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.76/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.76/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.76/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.76/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.76/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.76/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.76/1.18  tff(k2_mcart_1, type, k2_mcart_1: $i > $i).
% 1.76/1.18  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.76/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.76/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.76/1.18  tff(k1_mcart_1, type, k1_mcart_1: $i > $i).
% 1.76/1.18  
% 1.76/1.19  tff(f_53, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, k1_tarski(C))) => (r2_hidden(k1_mcart_1(A), B) & (k2_mcart_1(A) = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_mcart_1)).
% 1.76/1.19  tff(f_46, axiom, (![A, B, C]: (r2_hidden(A, k2_zfmisc_1(B, C)) => (r2_hidden(k1_mcart_1(A), B) & r2_hidden(k2_mcart_1(A), C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_mcart_1)).
% 1.76/1.19  tff(f_36, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 1.76/1.19  tff(f_38, axiom, (![A]: (k1_enumset1(A, A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t76_enumset1)).
% 1.76/1.19  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.76/1.19  tff(c_30, plain, (k2_mcart_1('#skF_3')!='#skF_5' | ~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.76/1.19  tff(c_44, plain, (~r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(splitLeft, [status(thm)], [c_30])).
% 1.76/1.19  tff(c_32, plain, (r2_hidden('#skF_3', k2_zfmisc_1('#skF_4', k1_tarski('#skF_5')))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.76/1.19  tff(c_99, plain, (![A_30, B_31, C_32]: (r2_hidden(k1_mcart_1(A_30), B_31) | ~r2_hidden(A_30, k2_zfmisc_1(B_31, C_32)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.76/1.19  tff(c_101, plain, (r2_hidden(k1_mcart_1('#skF_3'), '#skF_4')), inference(resolution, [status(thm)], [c_32, c_99])).
% 1.76/1.19  tff(c_105, plain, $false, inference(negUnitSimplification, [status(thm)], [c_44, c_101])).
% 1.76/1.19  tff(c_106, plain, (k2_mcart_1('#skF_3')!='#skF_5'), inference(splitRight, [status(thm)], [c_30])).
% 1.76/1.19  tff(c_167, plain, (![A_45, C_46, B_47]: (r2_hidden(k2_mcart_1(A_45), C_46) | ~r2_hidden(A_45, k2_zfmisc_1(B_47, C_46)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.76/1.19  tff(c_170, plain, (r2_hidden(k2_mcart_1('#skF_3'), k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_32, c_167])).
% 1.76/1.19  tff(c_108, plain, (![A_33, B_34]: (k1_enumset1(A_33, A_33, B_34)=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.76/1.19  tff(c_22, plain, (![A_9]: (k1_enumset1(A_9, A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.76/1.19  tff(c_115, plain, (![B_34]: (k2_tarski(B_34, B_34)=k1_tarski(B_34))), inference(superposition, [status(thm), theory('equality')], [c_108, c_22])).
% 1.76/1.19  tff(c_140, plain, (![D_37, B_38, A_39]: (D_37=B_38 | D_37=A_39 | ~r2_hidden(D_37, k2_tarski(A_39, B_38)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.76/1.19  tff(c_143, plain, (![D_37, B_34]: (D_37=B_34 | D_37=B_34 | ~r2_hidden(D_37, k1_tarski(B_34)))), inference(superposition, [status(thm), theory('equality')], [c_115, c_140])).
% 1.76/1.19  tff(c_182, plain, (k2_mcart_1('#skF_3')='#skF_5'), inference(resolution, [status(thm)], [c_170, c_143])).
% 1.76/1.19  tff(c_186, plain, $false, inference(negUnitSimplification, [status(thm)], [c_106, c_106, c_182])).
% 1.76/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.76/1.19  
% 1.76/1.19  Inference rules
% 1.76/1.19  ----------------------
% 1.76/1.19  #Ref     : 0
% 1.76/1.19  #Sup     : 32
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
% 1.76/1.19  #Demod        : 5
% 1.76/1.19  #Tautology    : 23
% 1.76/1.19  #SimpNegUnit  : 2
% 1.76/1.19  #BackRed      : 0
% 1.76/1.19  
% 1.76/1.19  #Partial instantiations: 0
% 1.76/1.19  #Strategies tried      : 1
% 1.76/1.19  
% 1.76/1.19  Timing (in seconds)
% 1.76/1.19  ----------------------
% 1.76/1.19  Preprocessing        : 0.30
% 1.76/1.19  Parsing              : 0.15
% 1.76/1.19  CNF conversion       : 0.02
% 1.76/1.19  Main loop            : 0.14
% 1.76/1.19  Inferencing          : 0.05
% 1.76/1.19  Reduction            : 0.04
% 1.76/1.19  Demodulation         : 0.03
% 1.76/1.19  BG Simplification    : 0.01
% 1.76/1.19  Subsumption          : 0.02
% 1.76/1.19  Abstraction          : 0.01
% 1.76/1.19  MUC search           : 0.00
% 1.76/1.20  Cooper               : 0.00
% 1.76/1.20  Total                : 0.46
% 1.76/1.20  Index Insertion      : 0.00
% 1.76/1.20  Index Deletion       : 0.00
% 1.76/1.20  Index Matching       : 0.00
% 1.76/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

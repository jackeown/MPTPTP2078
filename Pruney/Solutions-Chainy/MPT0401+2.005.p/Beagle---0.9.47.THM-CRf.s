%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:38 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   34 (  39 expanded)
%              Number of leaves         :   20 (  24 expanded)
%              Depth                    :    8
%              Number of atoms          :   41 (  55 expanded)
%              Number of equality atoms :   11 (  11 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > r1_setfam_1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_setfam_1(B,k1_tarski(A))
       => ! [C] :
            ( r2_hidden(C,B)
           => r1_tarski(C,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t24_setfam_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_32,plain,(
    ~ r1_tarski('#skF_7','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_34,plain,(
    r2_hidden('#skF_7','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_36,plain,(
    r1_setfam_1('#skF_6',k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_98,plain,(
    ! [A_43,B_44,C_45] :
      ( r2_hidden('#skF_4'(A_43,B_44,C_45),B_44)
      | ~ r2_hidden(C_45,A_43)
      | ~ r1_setfam_1(A_43,B_44) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_66,plain,(
    ! [D_33,B_34,A_35] :
      ( D_33 = B_34
      | D_33 = A_35
      | ~ r2_hidden(D_33,k2_tarski(A_35,B_34)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_76,plain,(
    ! [D_33,A_7] :
      ( D_33 = A_7
      | D_33 = A_7
      | ~ r2_hidden(D_33,k1_tarski(A_7)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_66])).

tff(c_115,plain,(
    ! [A_49,A_50,C_51] :
      ( '#skF_4'(A_49,k1_tarski(A_50),C_51) = A_50
      | ~ r2_hidden(C_51,A_49)
      | ~ r1_setfam_1(A_49,k1_tarski(A_50)) ) ),
    inference(resolution,[status(thm)],[c_98,c_76])).

tff(c_123,plain,(
    ! [C_52] :
      ( '#skF_4'('#skF_6',k1_tarski('#skF_5'),C_52) = '#skF_5'
      | ~ r2_hidden(C_52,'#skF_6') ) ),
    inference(resolution,[status(thm)],[c_36,c_115])).

tff(c_24,plain,(
    ! [C_20,A_10,B_11] :
      ( r1_tarski(C_20,'#skF_4'(A_10,B_11,C_20))
      | ~ r2_hidden(C_20,A_10)
      | ~ r1_setfam_1(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_129,plain,(
    ! [C_52] :
      ( r1_tarski(C_52,'#skF_5')
      | ~ r2_hidden(C_52,'#skF_6')
      | ~ r1_setfam_1('#skF_6',k1_tarski('#skF_5'))
      | ~ r2_hidden(C_52,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_24])).

tff(c_142,plain,(
    ! [C_53] :
      ( r1_tarski(C_53,'#skF_5')
      | ~ r2_hidden(C_53,'#skF_6') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_129])).

tff(c_153,plain,(
    r1_tarski('#skF_7','#skF_5') ),
    inference(resolution,[status(thm)],[c_34,c_142])).

tff(c_159,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_153])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n022.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:02:11 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.30  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.30  
% 2.06/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.31  %$ r2_hidden > r1_tarski > r1_setfam_1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2
% 2.06/1.31  
% 2.06/1.31  %Foreground sorts:
% 2.06/1.31  
% 2.06/1.31  
% 2.06/1.31  %Background operators:
% 2.06/1.31  
% 2.06/1.31  
% 2.06/1.31  %Foreground operators:
% 2.06/1.31  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.06/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.31  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.06/1.31  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.31  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.06/1.31  tff('#skF_7', type, '#skF_7': $i).
% 2.06/1.31  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.06/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.31  tff('#skF_5', type, '#skF_5': $i).
% 2.06/1.31  tff('#skF_6', type, '#skF_6': $i).
% 2.06/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.31  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.06/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.31  
% 2.06/1.31  tff(f_58, negated_conjecture, ~(![A, B]: (r1_setfam_1(B, k1_tarski(A)) => (![C]: (r2_hidden(C, B) => r1_tarski(C, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t24_setfam_1)).
% 2.06/1.31  tff(f_50, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.06/1.31  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.06/1.31  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.06/1.31  tff(c_32, plain, (~r1_tarski('#skF_7', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.06/1.31  tff(c_34, plain, (r2_hidden('#skF_7', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.06/1.31  tff(c_36, plain, (r1_setfam_1('#skF_6', k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.06/1.31  tff(c_98, plain, (![A_43, B_44, C_45]: (r2_hidden('#skF_4'(A_43, B_44, C_45), B_44) | ~r2_hidden(C_45, A_43) | ~r1_setfam_1(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.31  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 2.06/1.31  tff(c_66, plain, (![D_33, B_34, A_35]: (D_33=B_34 | D_33=A_35 | ~r2_hidden(D_33, k2_tarski(A_35, B_34)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.06/1.31  tff(c_76, plain, (![D_33, A_7]: (D_33=A_7 | D_33=A_7 | ~r2_hidden(D_33, k1_tarski(A_7)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_66])).
% 2.06/1.31  tff(c_115, plain, (![A_49, A_50, C_51]: ('#skF_4'(A_49, k1_tarski(A_50), C_51)=A_50 | ~r2_hidden(C_51, A_49) | ~r1_setfam_1(A_49, k1_tarski(A_50)))), inference(resolution, [status(thm)], [c_98, c_76])).
% 2.06/1.31  tff(c_123, plain, (![C_52]: ('#skF_4'('#skF_6', k1_tarski('#skF_5'), C_52)='#skF_5' | ~r2_hidden(C_52, '#skF_6'))), inference(resolution, [status(thm)], [c_36, c_115])).
% 2.06/1.31  tff(c_24, plain, (![C_20, A_10, B_11]: (r1_tarski(C_20, '#skF_4'(A_10, B_11, C_20)) | ~r2_hidden(C_20, A_10) | ~r1_setfam_1(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.31  tff(c_129, plain, (![C_52]: (r1_tarski(C_52, '#skF_5') | ~r2_hidden(C_52, '#skF_6') | ~r1_setfam_1('#skF_6', k1_tarski('#skF_5')) | ~r2_hidden(C_52, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_123, c_24])).
% 2.06/1.31  tff(c_142, plain, (![C_53]: (r1_tarski(C_53, '#skF_5') | ~r2_hidden(C_53, '#skF_6'))), inference(demodulation, [status(thm), theory('equality')], [c_36, c_129])).
% 2.06/1.31  tff(c_153, plain, (r1_tarski('#skF_7', '#skF_5')), inference(resolution, [status(thm)], [c_34, c_142])).
% 2.06/1.31  tff(c_159, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_153])).
% 2.06/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.31  
% 2.06/1.31  Inference rules
% 2.06/1.31  ----------------------
% 2.06/1.31  #Ref     : 0
% 2.06/1.31  #Sup     : 24
% 2.06/1.31  #Fact    : 0
% 2.06/1.31  #Define  : 0
% 2.06/1.31  #Split   : 0
% 2.06/1.31  #Chain   : 0
% 2.06/1.31  #Close   : 0
% 2.06/1.31  
% 2.06/1.31  Ordering : KBO
% 2.06/1.31  
% 2.06/1.31  Simplification rules
% 2.06/1.31  ----------------------
% 2.06/1.31  #Subsume      : 0
% 2.06/1.31  #Demod        : 4
% 2.06/1.31  #Tautology    : 11
% 2.06/1.31  #SimpNegUnit  : 1
% 2.06/1.31  #BackRed      : 0
% 2.06/1.31  
% 2.06/1.31  #Partial instantiations: 0
% 2.06/1.31  #Strategies tried      : 1
% 2.06/1.31  
% 2.06/1.31  Timing (in seconds)
% 2.06/1.31  ----------------------
% 2.06/1.32  Preprocessing        : 0.32
% 2.06/1.32  Parsing              : 0.16
% 2.06/1.32  CNF conversion       : 0.03
% 2.06/1.32  Main loop            : 0.14
% 2.06/1.32  Inferencing          : 0.05
% 2.06/1.32  Reduction            : 0.05
% 2.06/1.32  Demodulation         : 0.03
% 2.06/1.32  BG Simplification    : 0.02
% 2.06/1.32  Subsumption          : 0.03
% 2.06/1.32  Abstraction          : 0.01
% 2.06/1.32  MUC search           : 0.00
% 2.06/1.32  Cooper               : 0.00
% 2.06/1.32  Total                : 0.49
% 2.06/1.32  Index Insertion      : 0.00
% 2.06/1.32  Index Deletion       : 0.00
% 2.06/1.32  Index Matching       : 0.00
% 2.06/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------

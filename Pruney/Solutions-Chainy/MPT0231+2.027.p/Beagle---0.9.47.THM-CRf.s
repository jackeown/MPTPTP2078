%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:18 EST 2020

% Result     : Theorem 1.62s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   29 (  33 expanded)
%              Number of leaves         :   18 (  21 expanded)
%              Depth                    :    5
%              Number of atoms          :   28 (  37 expanded)
%              Number of equality atoms :   12 (  18 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_43,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_30,plain,(
    '#skF_6' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_32,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_12,plain,(
    ! [D_11,B_7] : r2_hidden(D_11,k2_tarski(D_11,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_68,plain,(
    ! [C_27,B_28,A_29] :
      ( r2_hidden(C_27,B_28)
      | ~ r2_hidden(C_27,A_29)
      | ~ r1_tarski(A_29,B_28) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_132,plain,(
    ! [D_40,B_41,B_42] :
      ( r2_hidden(D_40,B_41)
      | ~ r1_tarski(k2_tarski(D_40,B_42),B_41) ) ),
    inference(resolution,[status(thm)],[c_12,c_68])).

tff(c_145,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_6')) ),
    inference(resolution,[status(thm)],[c_32,c_132])).

tff(c_26,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_113,plain,(
    ! [D_37,B_38,A_39] :
      ( D_37 = B_38
      | D_37 = A_39
      | ~ r2_hidden(D_37,k2_tarski(A_39,B_38)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_157,plain,(
    ! [D_47,A_48] :
      ( D_47 = A_48
      | D_47 = A_48
      | ~ r2_hidden(D_47,k1_tarski(A_48)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_113])).

tff(c_160,plain,(
    '#skF_6' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_145,c_157])).

tff(c_174,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_30,c_160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n006.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:01:37 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.62/1.17  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.18  
% 1.62/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.62/1.18  %$ r2_hidden > r1_tarski > k2_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 1.62/1.18  
% 1.62/1.18  %Foreground sorts:
% 1.62/1.18  
% 1.62/1.18  
% 1.62/1.18  %Background operators:
% 1.62/1.18  
% 1.62/1.18  
% 1.62/1.18  %Foreground operators:
% 1.62/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.62/1.18  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.62/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.62/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.62/1.18  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.62/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.62/1.18  tff('#skF_5', type, '#skF_5': $i).
% 1.62/1.18  tff('#skF_6', type, '#skF_6': $i).
% 1.62/1.18  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.62/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.62/1.18  tff('#skF_4', type, '#skF_4': $i).
% 1.62/1.18  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.62/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.62/1.18  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.62/1.18  
% 1.85/1.19  tff(f_50, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 1.85/1.19  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.85/1.19  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 1.85/1.19  tff(f_43, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.85/1.19  tff(c_30, plain, ('#skF_6'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.85/1.19  tff(c_32, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.85/1.19  tff(c_12, plain, (![D_11, B_7]: (r2_hidden(D_11, k2_tarski(D_11, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.85/1.19  tff(c_68, plain, (![C_27, B_28, A_29]: (r2_hidden(C_27, B_28) | ~r2_hidden(C_27, A_29) | ~r1_tarski(A_29, B_28))), inference(cnfTransformation, [status(thm)], [f_32])).
% 1.85/1.19  tff(c_132, plain, (![D_40, B_41, B_42]: (r2_hidden(D_40, B_41) | ~r1_tarski(k2_tarski(D_40, B_42), B_41))), inference(resolution, [status(thm)], [c_12, c_68])).
% 1.85/1.19  tff(c_145, plain, (r2_hidden('#skF_4', k1_tarski('#skF_6'))), inference(resolution, [status(thm)], [c_32, c_132])).
% 1.85/1.19  tff(c_26, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.85/1.19  tff(c_113, plain, (![D_37, B_38, A_39]: (D_37=B_38 | D_37=A_39 | ~r2_hidden(D_37, k2_tarski(A_39, B_38)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.85/1.19  tff(c_157, plain, (![D_47, A_48]: (D_47=A_48 | D_47=A_48 | ~r2_hidden(D_47, k1_tarski(A_48)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_113])).
% 1.85/1.19  tff(c_160, plain, ('#skF_6'='#skF_4'), inference(resolution, [status(thm)], [c_145, c_157])).
% 1.85/1.19  tff(c_174, plain, $false, inference(negUnitSimplification, [status(thm)], [c_30, c_30, c_160])).
% 1.85/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.85/1.19  
% 1.85/1.19  Inference rules
% 1.85/1.19  ----------------------
% 1.85/1.19  #Ref     : 0
% 1.85/1.19  #Sup     : 30
% 1.85/1.19  #Fact    : 0
% 1.85/1.19  #Define  : 0
% 1.85/1.19  #Split   : 0
% 1.85/1.19  #Chain   : 0
% 1.85/1.19  #Close   : 0
% 1.85/1.19  
% 1.85/1.19  Ordering : KBO
% 1.85/1.19  
% 1.85/1.19  Simplification rules
% 1.85/1.19  ----------------------
% 1.85/1.19  #Subsume      : 2
% 1.85/1.19  #Demod        : 6
% 1.85/1.19  #Tautology    : 12
% 1.85/1.19  #SimpNegUnit  : 1
% 1.85/1.19  #BackRed      : 0
% 1.85/1.19  
% 1.85/1.19  #Partial instantiations: 0
% 1.85/1.19  #Strategies tried      : 1
% 1.85/1.19  
% 1.85/1.19  Timing (in seconds)
% 1.85/1.19  ----------------------
% 1.85/1.19  Preprocessing        : 0.29
% 1.85/1.19  Parsing              : 0.14
% 1.85/1.19  CNF conversion       : 0.02
% 1.85/1.19  Main loop            : 0.14
% 1.85/1.19  Inferencing          : 0.05
% 1.85/1.19  Reduction            : 0.04
% 1.85/1.19  Demodulation         : 0.03
% 1.85/1.19  BG Simplification    : 0.01
% 1.85/1.19  Subsumption          : 0.03
% 1.85/1.19  Abstraction          : 0.01
% 1.85/1.19  MUC search           : 0.00
% 1.85/1.19  Cooper               : 0.00
% 1.85/1.19  Total                : 0.45
% 1.85/1.19  Index Insertion      : 0.00
% 1.85/1.19  Index Deletion       : 0.00
% 1.85/1.19  Index Matching       : 0.00
% 1.85/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

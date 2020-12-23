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
% DateTime   : Thu Dec  3 09:47:44 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   30 (  40 expanded)
%              Number of leaves         :   17 (  23 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  49 expanded)
%              Number of equality atoms :   16 (  36 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => B = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_50,plain,(
    k2_tarski('#skF_6','#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_64,plain,(
    ! [D_18,B_19] : r2_hidden(D_18,k2_tarski(D_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_70,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_64])).

tff(c_44,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_104,plain,(
    ! [D_34,B_35,A_36] :
      ( D_34 = B_35
      | D_34 = A_36
      | ~ r2_hidden(D_34,k2_tarski(A_36,B_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_121,plain,(
    ! [D_37,A_38] :
      ( D_37 = A_38
      | D_37 = A_38
      | ~ r2_hidden(D_37,k1_tarski(A_38)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_104])).

tff(c_132,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_70,c_121])).

tff(c_72,plain,(
    ! [D_21,A_22] : r2_hidden(D_21,k2_tarski(A_22,D_21)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_78,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_72])).

tff(c_131,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_78,c_121])).

tff(c_48,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_137,plain,(
    '#skF_5' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_48])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_132,c_137])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n025.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 13:12:20 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.21  
% 1.93/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.21  %$ r2_hidden > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_3 > #skF_1
% 1.93/1.21  
% 1.93/1.21  %Foreground sorts:
% 1.93/1.21  
% 1.93/1.21  
% 1.93/1.21  %Background operators:
% 1.93/1.21  
% 1.93/1.21  
% 1.93/1.21  %Foreground operators:
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.21  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.93/1.21  tff('#skF_7', type, '#skF_7': $i).
% 1.93/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.21  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.21  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 1.93/1.21  tff('#skF_6', type, '#skF_6': $i).
% 1.93/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.21  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.93/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.21  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 1.93/1.21  
% 1.93/1.22  tff(f_58, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (B = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 1.93/1.22  tff(f_49, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.93/1.22  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.93/1.22  tff(c_50, plain, (k2_tarski('#skF_6', '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.93/1.22  tff(c_64, plain, (![D_18, B_19]: (r2_hidden(D_18, k2_tarski(D_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.93/1.22  tff(c_70, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_64])).
% 1.93/1.22  tff(c_44, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.93/1.22  tff(c_104, plain, (![D_34, B_35, A_36]: (D_34=B_35 | D_34=A_36 | ~r2_hidden(D_34, k2_tarski(A_36, B_35)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.93/1.22  tff(c_121, plain, (![D_37, A_38]: (D_37=A_38 | D_37=A_38 | ~r2_hidden(D_37, k1_tarski(A_38)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_104])).
% 1.93/1.22  tff(c_132, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_70, c_121])).
% 1.93/1.22  tff(c_72, plain, (![D_21, A_22]: (r2_hidden(D_21, k2_tarski(A_22, D_21)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.93/1.22  tff(c_78, plain, (r2_hidden('#skF_7', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_72])).
% 1.93/1.22  tff(c_131, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_78, c_121])).
% 1.93/1.22  tff(c_48, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.93/1.22  tff(c_137, plain, ('#skF_5'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_131, c_48])).
% 1.93/1.22  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_132, c_137])).
% 1.93/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.22  
% 1.93/1.22  Inference rules
% 1.93/1.22  ----------------------
% 1.93/1.22  #Ref     : 0
% 1.93/1.22  #Sup     : 28
% 1.93/1.22  #Fact    : 0
% 1.93/1.22  #Define  : 0
% 1.93/1.22  #Split   : 0
% 1.93/1.22  #Chain   : 0
% 1.93/1.22  #Close   : 0
% 1.93/1.22  
% 1.93/1.22  Ordering : KBO
% 1.93/1.22  
% 1.93/1.22  Simplification rules
% 1.93/1.22  ----------------------
% 1.93/1.22  #Subsume      : 1
% 1.93/1.22  #Demod        : 12
% 1.93/1.22  #Tautology    : 22
% 1.93/1.22  #SimpNegUnit  : 0
% 1.93/1.22  #BackRed      : 5
% 1.93/1.22  
% 1.93/1.22  #Partial instantiations: 0
% 1.93/1.22  #Strategies tried      : 1
% 1.93/1.22  
% 1.93/1.22  Timing (in seconds)
% 1.93/1.22  ----------------------
% 1.93/1.22  Preprocessing        : 0.30
% 1.93/1.22  Parsing              : 0.14
% 1.93/1.22  CNF conversion       : 0.03
% 1.93/1.22  Main loop            : 0.15
% 1.93/1.22  Inferencing          : 0.04
% 1.93/1.22  Reduction            : 0.05
% 1.93/1.22  Demodulation         : 0.04
% 1.93/1.22  BG Simplification    : 0.02
% 1.93/1.22  Subsumption          : 0.03
% 1.93/1.22  Abstraction          : 0.01
% 1.93/1.22  MUC search           : 0.00
% 1.93/1.22  Cooper               : 0.00
% 1.93/1.22  Total                : 0.47
% 1.93/1.22  Index Insertion      : 0.00
% 1.93/1.23  Index Deletion       : 0.00
% 1.93/1.23  Index Matching       : 0.00
% 1.93/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

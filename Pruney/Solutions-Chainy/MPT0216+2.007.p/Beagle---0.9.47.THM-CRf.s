%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:44 EST 2020

% Result     : Theorem 1.93s
% Output     : CNFRefutation 1.93s
% Verified   : 
% Statistics : Number of formulae       :   33 (  43 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    5
%              Number of atoms          :   24 (  49 expanded)
%              Number of equality atoms :   16 (  36 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_53,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k1_tarski(A) = k2_tarski(B,C)
       => B = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t9_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_36,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_36,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_50,plain,(
    ! [D_36,B_37] : r2_hidden(D_36,k2_tarski(D_36,B_37)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_56,plain,(
    r2_hidden('#skF_4',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_50])).

tff(c_20,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_75,plain,(
    ! [D_43,B_44,A_45] :
      ( D_43 = B_44
      | D_43 = A_45
      | ~ r2_hidden(D_43,k2_tarski(A_45,B_44)) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_92,plain,(
    ! [D_46,A_47] :
      ( D_46 = A_47
      | D_46 = A_47
      | ~ r2_hidden(D_46,k1_tarski(A_47)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_75])).

tff(c_103,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_56,c_92])).

tff(c_58,plain,(
    ! [D_39,A_40] : r2_hidden(D_39,k2_tarski(A_40,D_39)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_64,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_58])).

tff(c_102,plain,(
    '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_64,c_92])).

tff(c_34,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_108,plain,(
    '#skF_3' != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_34])).

tff(c_122,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_103,c_108])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n011.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 16:37:27 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.93/1.24  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.24  
% 1.93/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.25  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 1.93/1.25  
% 1.93/1.25  %Foreground sorts:
% 1.93/1.25  
% 1.93/1.25  
% 1.93/1.25  %Background operators:
% 1.93/1.25  
% 1.93/1.25  
% 1.93/1.25  %Foreground operators:
% 1.93/1.25  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.93/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.93/1.25  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.93/1.25  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.93/1.25  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.93/1.25  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.93/1.25  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.93/1.25  tff('#skF_5', type, '#skF_5': $i).
% 1.93/1.25  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.93/1.25  tff('#skF_3', type, '#skF_3': $i).
% 1.93/1.25  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.93/1.25  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.25  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.93/1.25  tff('#skF_4', type, '#skF_4': $i).
% 1.93/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.93/1.25  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.93/1.25  
% 1.93/1.25  tff(f_53, negated_conjecture, ~(![A, B, C]: ((k1_tarski(A) = k2_tarski(B, C)) => (B = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t9_zfmisc_1)).
% 1.93/1.25  tff(f_34, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.93/1.25  tff(f_36, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.93/1.25  tff(c_36, plain, (k2_tarski('#skF_4', '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.93/1.25  tff(c_50, plain, (![D_36, B_37]: (r2_hidden(D_36, k2_tarski(D_36, B_37)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.93/1.25  tff(c_56, plain, (r2_hidden('#skF_4', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_50])).
% 1.93/1.25  tff(c_20, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.93/1.25  tff(c_75, plain, (![D_43, B_44, A_45]: (D_43=B_44 | D_43=A_45 | ~r2_hidden(D_43, k2_tarski(A_45, B_44)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.93/1.25  tff(c_92, plain, (![D_46, A_47]: (D_46=A_47 | D_46=A_47 | ~r2_hidden(D_46, k1_tarski(A_47)))), inference(superposition, [status(thm), theory('equality')], [c_20, c_75])).
% 1.93/1.25  tff(c_103, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_56, c_92])).
% 1.93/1.25  tff(c_58, plain, (![D_39, A_40]: (r2_hidden(D_39, k2_tarski(A_40, D_39)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.93/1.25  tff(c_64, plain, (r2_hidden('#skF_5', k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_36, c_58])).
% 1.93/1.25  tff(c_102, plain, ('#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_64, c_92])).
% 1.93/1.25  tff(c_34, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.93/1.25  tff(c_108, plain, ('#skF_3'!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_34])).
% 1.93/1.25  tff(c_122, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_103, c_108])).
% 1.93/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.93/1.25  
% 1.93/1.25  Inference rules
% 1.93/1.25  ----------------------
% 1.93/1.25  #Ref     : 0
% 1.93/1.25  #Sup     : 21
% 1.93/1.25  #Fact    : 0
% 1.93/1.25  #Define  : 0
% 1.93/1.25  #Split   : 0
% 1.93/1.25  #Chain   : 0
% 1.93/1.25  #Close   : 0
% 1.93/1.25  
% 1.93/1.25  Ordering : KBO
% 1.93/1.25  
% 1.93/1.25  Simplification rules
% 1.93/1.25  ----------------------
% 1.93/1.25  #Subsume      : 0
% 1.93/1.25  #Demod        : 9
% 1.93/1.25  #Tautology    : 16
% 1.93/1.25  #SimpNegUnit  : 0
% 1.93/1.25  #BackRed      : 5
% 1.93/1.25  
% 1.93/1.25  #Partial instantiations: 0
% 1.93/1.25  #Strategies tried      : 1
% 1.93/1.25  
% 1.93/1.25  Timing (in seconds)
% 1.93/1.25  ----------------------
% 1.93/1.26  Preprocessing        : 0.33
% 1.93/1.26  Parsing              : 0.16
% 1.93/1.26  CNF conversion       : 0.02
% 1.93/1.26  Main loop            : 0.10
% 1.93/1.26  Inferencing          : 0.03
% 1.93/1.26  Reduction            : 0.04
% 1.93/1.26  Demodulation         : 0.03
% 1.93/1.26  BG Simplification    : 0.02
% 1.93/1.26  Subsumption          : 0.02
% 1.93/1.26  Abstraction          : 0.01
% 1.93/1.26  MUC search           : 0.00
% 1.93/1.26  Cooper               : 0.00
% 1.93/1.26  Total                : 0.45
% 1.93/1.26  Index Insertion      : 0.00
% 1.93/1.26  Index Deletion       : 0.00
% 1.93/1.26  Index Matching       : 0.00
% 1.93/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------

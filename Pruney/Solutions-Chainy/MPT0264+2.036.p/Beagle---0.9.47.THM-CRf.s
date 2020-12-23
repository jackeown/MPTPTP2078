%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n013.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:25 EST 2020

% Result     : Theorem 10.54s
% Output     : CNFRefutation 10.56s
% Verified   : 
% Statistics : Number of formulae       :   28 (  30 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   31 (  37 expanded)
%              Number of equality atoms :   17 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4

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

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_57,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_32,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_34,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_36,plain,(
    k3_xboole_0(k2_tarski('#skF_3','#skF_4'),'#skF_5') = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_20,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k4_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_213,plain,(
    ! [B_50,A_51,C_52] :
      ( B_50 = A_51
      | r2_hidden(B_50,C_52)
      | k4_xboole_0(k2_tarski(A_51,B_50),C_52) != k1_tarski(A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_2999,plain,(
    ! [B_172,A_173,B_174] :
      ( B_172 = A_173
      | r2_hidden(B_172,k4_xboole_0(k2_tarski(A_173,B_172),B_174))
      | k3_xboole_0(k2_tarski(A_173,B_172),B_174) != k1_tarski(A_173) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_213])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_15748,plain,(
    ! [B_410,B_411,A_412] :
      ( ~ r2_hidden(B_410,B_411)
      | B_410 = A_412
      | k3_xboole_0(k2_tarski(A_412,B_410),B_411) != k1_tarski(A_412) ) ),
    inference(resolution,[status(thm)],[c_2999,c_4])).

tff(c_15765,plain,
    ( ~ r2_hidden('#skF_4','#skF_5')
    | '#skF_3' = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_15748])).

tff(c_15772,plain,(
    '#skF_3' = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_15765])).

tff(c_15774,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_15772])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n013.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:49:24 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.54/3.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.56/3.56  
% 10.56/3.56  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.56/3.56  %$ r2_hidden > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_3 > #skF_2 > #skF_4
% 10.56/3.56  
% 10.56/3.56  %Foreground sorts:
% 10.56/3.56  
% 10.56/3.56  
% 10.56/3.56  %Background operators:
% 10.56/3.56  
% 10.56/3.56  
% 10.56/3.56  %Foreground operators:
% 10.56/3.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 10.56/3.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.56/3.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.56/3.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 10.56/3.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.56/3.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.56/3.56  tff('#skF_5', type, '#skF_5': $i).
% 10.56/3.56  tff('#skF_3', type, '#skF_3': $i).
% 10.56/3.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 10.56/3.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.56/3.56  tff('#skF_4', type, '#skF_4': $i).
% 10.56/3.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.56/3.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.56/3.56  
% 10.56/3.57  tff(f_57, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 10.56/3.57  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 10.56/3.57  tff(f_48, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 10.56/3.57  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 10.56/3.57  tff(c_32, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.56/3.57  tff(c_34, plain, (r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.56/3.57  tff(c_36, plain, (k3_xboole_0(k2_tarski('#skF_3', '#skF_4'), '#skF_5')=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.56/3.57  tff(c_20, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k4_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.56/3.57  tff(c_213, plain, (![B_50, A_51, C_52]: (B_50=A_51 | r2_hidden(B_50, C_52) | k4_xboole_0(k2_tarski(A_51, B_50), C_52)!=k1_tarski(A_51))), inference(cnfTransformation, [status(thm)], [f_48])).
% 10.56/3.57  tff(c_2999, plain, (![B_172, A_173, B_174]: (B_172=A_173 | r2_hidden(B_172, k4_xboole_0(k2_tarski(A_173, B_172), B_174)) | k3_xboole_0(k2_tarski(A_173, B_172), B_174)!=k1_tarski(A_173))), inference(superposition, [status(thm), theory('equality')], [c_20, c_213])).
% 10.56/3.57  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 10.56/3.57  tff(c_15748, plain, (![B_410, B_411, A_412]: (~r2_hidden(B_410, B_411) | B_410=A_412 | k3_xboole_0(k2_tarski(A_412, B_410), B_411)!=k1_tarski(A_412))), inference(resolution, [status(thm)], [c_2999, c_4])).
% 10.56/3.57  tff(c_15765, plain, (~r2_hidden('#skF_4', '#skF_5') | '#skF_3'='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_36, c_15748])).
% 10.56/3.57  tff(c_15772, plain, ('#skF_3'='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_34, c_15765])).
% 10.56/3.57  tff(c_15774, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_15772])).
% 10.56/3.57  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.56/3.57  
% 10.56/3.57  Inference rules
% 10.56/3.57  ----------------------
% 10.56/3.57  #Ref     : 0
% 10.56/3.57  #Sup     : 4204
% 10.56/3.57  #Fact    : 0
% 10.56/3.57  #Define  : 0
% 10.56/3.57  #Split   : 4
% 10.56/3.57  #Chain   : 0
% 10.56/3.57  #Close   : 0
% 10.56/3.57  
% 10.56/3.57  Ordering : KBO
% 10.56/3.57  
% 10.56/3.57  Simplification rules
% 10.56/3.57  ----------------------
% 10.56/3.57  #Subsume      : 1337
% 10.56/3.57  #Demod        : 1215
% 10.56/3.57  #Tautology    : 480
% 10.56/3.57  #SimpNegUnit  : 197
% 10.56/3.57  #BackRed      : 32
% 10.56/3.57  
% 10.56/3.57  #Partial instantiations: 0
% 10.56/3.57  #Strategies tried      : 1
% 10.56/3.57  
% 10.56/3.57  Timing (in seconds)
% 10.56/3.57  ----------------------
% 10.56/3.57  Preprocessing        : 0.29
% 10.56/3.57  Parsing              : 0.15
% 10.56/3.57  CNF conversion       : 0.02
% 10.56/3.57  Main loop            : 2.53
% 10.56/3.57  Inferencing          : 0.68
% 10.56/3.57  Reduction            : 0.88
% 10.56/3.57  Demodulation         : 0.66
% 10.56/3.57  BG Simplification    : 0.10
% 10.56/3.57  Subsumption          : 0.69
% 10.56/3.57  Abstraction          : 0.13
% 10.56/3.57  MUC search           : 0.00
% 10.56/3.57  Cooper               : 0.00
% 10.56/3.58  Total                : 2.85
% 10.56/3.58  Index Insertion      : 0.00
% 10.56/3.58  Index Deletion       : 0.00
% 10.56/3.58  Index Matching       : 0.00
% 10.56/3.58  BG Taut test         : 0.00
%------------------------------------------------------------------------------

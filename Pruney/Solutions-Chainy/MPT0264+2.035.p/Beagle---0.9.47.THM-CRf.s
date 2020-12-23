%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:25 EST 2020

% Result     : Theorem 1.99s
% Output     : CNFRefutation 1.99s
% Verified   : 
% Statistics : Number of formulae       :   34 (  39 expanded)
%              Number of leaves         :   21 (  25 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  48 expanded)
%              Number of equality atoms :   15 (  25 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k3_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
          & r2_hidden(B,C)
          & A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t59_zfmisc_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_34,axiom,(
    ! [A,B,C] :
      ( C = k3_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d4_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(c_46,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_48,plain,(
    r2_hidden('#skF_6','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_24,plain,(
    ! [D_14,A_9] : r2_hidden(D_14,k2_tarski(A_9,D_14)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_50,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_185,plain,(
    ! [D_50,A_51,B_52] :
      ( r2_hidden(D_50,k3_xboole_0(A_51,B_52))
      | ~ r2_hidden(D_50,B_52)
      | ~ r2_hidden(D_50,A_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_200,plain,(
    ! [D_53] :
      ( r2_hidden(D_53,k1_tarski('#skF_5'))
      | ~ r2_hidden(D_53,'#skF_7')
      | ~ r2_hidden(D_53,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_185])).

tff(c_207,plain,
    ( r2_hidden('#skF_6',k1_tarski('#skF_5'))
    | ~ r2_hidden('#skF_6','#skF_7') ),
    inference(resolution,[status(thm)],[c_24,c_200])).

tff(c_215,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_48,c_207])).

tff(c_40,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_113,plain,(
    ! [D_39,B_40,A_41] :
      ( D_39 = B_40
      | D_39 = A_41
      | ~ r2_hidden(D_39,k2_tarski(A_41,B_40)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_125,plain,(
    ! [D_39,A_15] :
      ( D_39 = A_15
      | D_39 = A_15
      | ~ r2_hidden(D_39,k1_tarski(A_15)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_113])).

tff(c_224,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_215,c_125])).

tff(c_235,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_46,c_46,c_224])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:24:23 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.99/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.28  
% 1.99/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.28  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 1.99/1.28  
% 1.99/1.28  %Foreground sorts:
% 1.99/1.28  
% 1.99/1.28  
% 1.99/1.28  %Background operators:
% 1.99/1.28  
% 1.99/1.28  
% 1.99/1.28  %Foreground operators:
% 1.99/1.28  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.99/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.99/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.99/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.99/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.99/1.28  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 1.99/1.28  tff('#skF_7', type, '#skF_7': $i).
% 1.99/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.99/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.99/1.28  tff('#skF_5', type, '#skF_5': $i).
% 1.99/1.28  tff('#skF_6', type, '#skF_6': $i).
% 1.99/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.99/1.28  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.99/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.99/1.28  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.99/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.99/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.99/1.28  
% 1.99/1.29  tff(f_60, negated_conjecture, ~(![A, B, C]: ~(((k3_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) & r2_hidden(B, C)) & ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t59_zfmisc_1)).
% 1.99/1.29  tff(f_45, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.99/1.29  tff(f_34, axiom, (![A, B, C]: ((C = k3_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d4_xboole_0)).
% 1.99/1.29  tff(f_47, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.99/1.29  tff(c_46, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.99/1.29  tff(c_48, plain, (r2_hidden('#skF_6', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.99/1.29  tff(c_24, plain, (![D_14, A_9]: (r2_hidden(D_14, k2_tarski(A_9, D_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.99/1.29  tff(c_50, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.99/1.29  tff(c_185, plain, (![D_50, A_51, B_52]: (r2_hidden(D_50, k3_xboole_0(A_51, B_52)) | ~r2_hidden(D_50, B_52) | ~r2_hidden(D_50, A_51))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.99/1.29  tff(c_200, plain, (![D_53]: (r2_hidden(D_53, k1_tarski('#skF_5')) | ~r2_hidden(D_53, '#skF_7') | ~r2_hidden(D_53, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_50, c_185])).
% 1.99/1.29  tff(c_207, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5')) | ~r2_hidden('#skF_6', '#skF_7')), inference(resolution, [status(thm)], [c_24, c_200])).
% 1.99/1.29  tff(c_215, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_48, c_207])).
% 1.99/1.29  tff(c_40, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.99/1.29  tff(c_113, plain, (![D_39, B_40, A_41]: (D_39=B_40 | D_39=A_41 | ~r2_hidden(D_39, k2_tarski(A_41, B_40)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.99/1.29  tff(c_125, plain, (![D_39, A_15]: (D_39=A_15 | D_39=A_15 | ~r2_hidden(D_39, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_113])).
% 1.99/1.29  tff(c_224, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_215, c_125])).
% 1.99/1.29  tff(c_235, plain, $false, inference(negUnitSimplification, [status(thm)], [c_46, c_46, c_224])).
% 1.99/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.99/1.29  
% 1.99/1.29  Inference rules
% 1.99/1.29  ----------------------
% 1.99/1.29  #Ref     : 0
% 1.99/1.29  #Sup     : 42
% 1.99/1.29  #Fact    : 0
% 1.99/1.29  #Define  : 0
% 1.99/1.29  #Split   : 0
% 1.99/1.29  #Chain   : 0
% 1.99/1.29  #Close   : 0
% 1.99/1.29  
% 1.99/1.29  Ordering : KBO
% 1.99/1.29  
% 1.99/1.29  Simplification rules
% 1.99/1.29  ----------------------
% 1.99/1.29  #Subsume      : 0
% 1.99/1.29  #Demod        : 8
% 1.99/1.29  #Tautology    : 26
% 1.99/1.29  #SimpNegUnit  : 3
% 1.99/1.29  #BackRed      : 0
% 1.99/1.29  
% 1.99/1.29  #Partial instantiations: 0
% 1.99/1.29  #Strategies tried      : 1
% 1.99/1.29  
% 1.99/1.29  Timing (in seconds)
% 1.99/1.29  ----------------------
% 1.99/1.30  Preprocessing        : 0.32
% 1.99/1.30  Parsing              : 0.16
% 1.99/1.30  CNF conversion       : 0.03
% 1.99/1.30  Main loop            : 0.17
% 1.99/1.30  Inferencing          : 0.06
% 1.99/1.30  Reduction            : 0.06
% 1.99/1.30  Demodulation         : 0.05
% 1.99/1.30  BG Simplification    : 0.01
% 1.99/1.30  Subsumption          : 0.03
% 1.99/1.30  Abstraction          : 0.01
% 1.99/1.30  MUC search           : 0.00
% 1.99/1.30  Cooper               : 0.00
% 1.99/1.30  Total                : 0.52
% 1.99/1.30  Index Insertion      : 0.00
% 1.99/1.30  Index Deletion       : 0.00
% 1.99/1.30  Index Matching       : 0.00
% 1.99/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------

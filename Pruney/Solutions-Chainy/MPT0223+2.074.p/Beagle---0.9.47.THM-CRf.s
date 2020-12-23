%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:26 EST 2020

% Result     : Theorem 2.47s
% Output     : CNFRefutation 2.47s
% Verified   : 
% Statistics : Number of formulae       :   36 (  41 expanded)
%              Number of leaves         :   22 (  26 expanded)
%              Depth                    :    8
%              Number of atoms          :   34 (  47 expanded)
%              Number of equality atoms :   11 (  18 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_8 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_6',type,(
    '#skF_6': ( $i * $i * $i ) > $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_58,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_24,plain,(
    ! [C_13] : r2_hidden(C_13,k1_tarski(C_13)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_60,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_404,plain,(
    ! [D_641,A_642,B_643] :
      ( r2_hidden(D_641,k4_xboole_0(A_642,B_643))
      | r2_hidden(D_641,B_643)
      | ~ r2_hidden(D_641,A_642) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_102,plain,(
    ! [A_42,B_43] : k4_xboole_0(A_42,k4_xboole_0(A_42,B_43)) = k3_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_114,plain,(
    ! [D_6,A_42,B_43] :
      ( ~ r2_hidden(D_6,k4_xboole_0(A_42,B_43))
      | ~ r2_hidden(D_6,k3_xboole_0(A_42,B_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_4])).

tff(c_557,plain,(
    ! [D_766,A_767,B_768] :
      ( ~ r2_hidden(D_766,k3_xboole_0(A_767,B_768))
      | r2_hidden(D_766,B_768)
      | ~ r2_hidden(D_766,A_767) ) ),
    inference(resolution,[status(thm)],[c_404,c_114])).

tff(c_757,plain,(
    ! [D_960] :
      ( ~ r2_hidden(D_960,k1_tarski('#skF_7'))
      | r2_hidden(D_960,k1_tarski('#skF_8'))
      | ~ r2_hidden(D_960,k1_tarski('#skF_7')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_60,c_557])).

tff(c_781,plain,
    ( r2_hidden('#skF_7',k1_tarski('#skF_8'))
    | ~ r2_hidden('#skF_7',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_24,c_757])).

tff(c_785,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_24,c_781])).

tff(c_22,plain,(
    ! [C_13,A_9] :
      ( C_13 = A_9
      | ~ r2_hidden(C_13,k1_tarski(A_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_788,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_785,c_22])).

tff(c_822,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_58,c_788])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n019.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:54:22 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.47/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.39  
% 2.47/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.39  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_6 > #skF_7 > #skF_3 > #skF_5 > #skF_2 > #skF_8 > #skF_4
% 2.47/1.39  
% 2.47/1.39  %Foreground sorts:
% 2.47/1.39  
% 2.47/1.39  
% 2.47/1.39  %Background operators:
% 2.47/1.39  
% 2.47/1.39  
% 2.47/1.39  %Foreground operators:
% 2.47/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.47/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.47/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.47/1.39  tff('#skF_6', type, '#skF_6': ($i * $i * $i) > $i).
% 2.47/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.47/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.47/1.39  tff('#skF_7', type, '#skF_7': $i).
% 2.47/1.39  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.47/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.47/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.47/1.39  tff('#skF_5', type, '#skF_5': ($i * $i * $i) > $i).
% 2.47/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.47/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.47/1.39  tff('#skF_8', type, '#skF_8': $i).
% 2.47/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.47/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.47/1.39  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.47/1.39  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.47/1.39  
% 2.47/1.40  tff(f_64, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 2.47/1.40  tff(f_44, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.47/1.40  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.47/1.40  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.47/1.40  tff(c_58, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.47/1.40  tff(c_24, plain, (![C_13]: (r2_hidden(C_13, k1_tarski(C_13)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.47/1.40  tff(c_60, plain, (k3_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_64])).
% 2.47/1.40  tff(c_404, plain, (![D_641, A_642, B_643]: (r2_hidden(D_641, k4_xboole_0(A_642, B_643)) | r2_hidden(D_641, B_643) | ~r2_hidden(D_641, A_642))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.40  tff(c_102, plain, (![A_42, B_43]: (k4_xboole_0(A_42, k4_xboole_0(A_42, B_43))=k3_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.47/1.40  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.47/1.40  tff(c_114, plain, (![D_6, A_42, B_43]: (~r2_hidden(D_6, k4_xboole_0(A_42, B_43)) | ~r2_hidden(D_6, k3_xboole_0(A_42, B_43)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_4])).
% 2.47/1.40  tff(c_557, plain, (![D_766, A_767, B_768]: (~r2_hidden(D_766, k3_xboole_0(A_767, B_768)) | r2_hidden(D_766, B_768) | ~r2_hidden(D_766, A_767))), inference(resolution, [status(thm)], [c_404, c_114])).
% 2.47/1.40  tff(c_757, plain, (![D_960]: (~r2_hidden(D_960, k1_tarski('#skF_7')) | r2_hidden(D_960, k1_tarski('#skF_8')) | ~r2_hidden(D_960, k1_tarski('#skF_7')))), inference(superposition, [status(thm), theory('equality')], [c_60, c_557])).
% 2.47/1.40  tff(c_781, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8')) | ~r2_hidden('#skF_7', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_24, c_757])).
% 2.47/1.40  tff(c_785, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_24, c_781])).
% 2.47/1.40  tff(c_22, plain, (![C_13, A_9]: (C_13=A_9 | ~r2_hidden(C_13, k1_tarski(A_9)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.47/1.40  tff(c_788, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_785, c_22])).
% 2.47/1.40  tff(c_822, plain, $false, inference(negUnitSimplification, [status(thm)], [c_58, c_788])).
% 2.47/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.47/1.40  
% 2.47/1.40  Inference rules
% 2.47/1.40  ----------------------
% 2.47/1.40  #Ref     : 0
% 2.47/1.40  #Sup     : 99
% 2.47/1.40  #Fact    : 0
% 2.47/1.40  #Define  : 0
% 2.47/1.40  #Split   : 0
% 2.47/1.40  #Chain   : 0
% 2.47/1.40  #Close   : 0
% 2.47/1.40  
% 2.47/1.40  Ordering : KBO
% 2.47/1.40  
% 2.47/1.40  Simplification rules
% 2.47/1.40  ----------------------
% 2.47/1.40  #Subsume      : 6
% 2.47/1.40  #Demod        : 12
% 2.47/1.40  #Tautology    : 31
% 2.47/1.40  #SimpNegUnit  : 1
% 2.47/1.40  #BackRed      : 0
% 2.47/1.40  
% 2.47/1.40  #Partial instantiations: 420
% 2.47/1.40  #Strategies tried      : 1
% 2.47/1.40  
% 2.47/1.40  Timing (in seconds)
% 2.47/1.40  ----------------------
% 2.47/1.40  Preprocessing        : 0.30
% 2.47/1.40  Parsing              : 0.14
% 2.47/1.40  CNF conversion       : 0.02
% 2.47/1.40  Main loop            : 0.31
% 2.47/1.40  Inferencing          : 0.15
% 2.47/1.40  Reduction            : 0.08
% 2.47/1.40  Demodulation         : 0.06
% 2.47/1.40  BG Simplification    : 0.02
% 2.47/1.40  Subsumption          : 0.05
% 2.47/1.40  Abstraction          : 0.01
% 2.47/1.40  MUC search           : 0.00
% 2.47/1.40  Cooper               : 0.00
% 2.47/1.40  Total                : 0.63
% 2.47/1.40  Index Insertion      : 0.00
% 2.47/1.40  Index Deletion       : 0.00
% 2.47/1.40  Index Matching       : 0.00
% 2.47/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:38 EST 2020

% Result     : Theorem 18.10s
% Output     : CNFRefutation 18.10s
% Verified   : 
% Statistics : Number of formulae       :   44 (  58 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  79 expanded)
%              Number of equality atoms :   20 (  34 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(k2_xboole_0(A,B),B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t40_xboole_1)).

tff(f_78,negated_conjecture,(
    ~ ! [A,B] :
        ( ~ r2_hidden(A,B)
       => k4_xboole_0(k2_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t141_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_56,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_22,plain,(
    ! [A_9,B_10] : k4_xboole_0(k2_xboole_0(A_9,B_10),B_10) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_62,plain,(
    k4_xboole_0(k2_xboole_0('#skF_6',k1_tarski('#skF_5')),k1_tarski('#skF_5')) != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_65,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_62])).

tff(c_64,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_18,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),C_3)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2900,plain,(
    ! [A_3473,B_3474,C_3475] :
      ( ~ r2_hidden('#skF_1'(A_3473,B_3474,C_3475),C_3475)
      | r2_hidden('#skF_2'(A_3473,B_3474,C_3475),C_3475)
      | k4_xboole_0(A_3473,B_3474) = C_3475 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_2910,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_2'(A_1,B_2,A_1),A_1)
      | k4_xboole_0(A_1,B_2) = A_1 ) ),
    inference(resolution,[status(thm)],[c_18,c_2900])).

tff(c_12,plain,(
    ! [A_1,B_2,C_3] :
      ( r2_hidden('#skF_1'(A_1,B_2,C_3),A_1)
      | r2_hidden('#skF_2'(A_1,B_2,C_3),B_2)
      | ~ r2_hidden('#skF_2'(A_1,B_2,C_3),A_1)
      | k4_xboole_0(A_1,B_2) = C_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_3699,plain,(
    ! [A_4386,B_4387,C_4388] :
      ( ~ r2_hidden('#skF_1'(A_4386,B_4387,C_4388),C_4388)
      | r2_hidden('#skF_2'(A_4386,B_4387,C_4388),B_4387)
      | ~ r2_hidden('#skF_2'(A_4386,B_4387,C_4388),A_4386)
      | k4_xboole_0(A_4386,B_4387) = C_4388 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_8876,plain,(
    ! [A_7786,B_7787] :
      ( r2_hidden('#skF_2'(A_7786,B_7787,A_7786),B_7787)
      | ~ r2_hidden('#skF_2'(A_7786,B_7787,A_7786),A_7786)
      | k4_xboole_0(A_7786,B_7787) = A_7786 ) ),
    inference(resolution,[status(thm)],[c_12,c_3699])).

tff(c_23004,plain,(
    ! [A_11751,B_11752] :
      ( r2_hidden('#skF_2'(A_11751,B_11752,A_11751),B_11752)
      | k4_xboole_0(A_11751,B_11752) = A_11751 ) ),
    inference(resolution,[status(thm)],[c_2910,c_8876])).

tff(c_34,plain,(
    ! [C_24,A_20] :
      ( C_24 = A_20
      | ~ r2_hidden(C_24,k1_tarski(A_20)) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_47808,plain,(
    ! [A_13719,A_13720] :
      ( '#skF_2'(A_13719,k1_tarski(A_13720),A_13719) = A_13720
      | k4_xboole_0(A_13719,k1_tarski(A_13720)) = A_13719 ) ),
    inference(resolution,[status(thm)],[c_23004,c_34])).

tff(c_48148,plain,(
    '#skF_2'('#skF_6',k1_tarski('#skF_5'),'#skF_6') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_47808,c_65])).

tff(c_48163,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_48148,c_2910])).

tff(c_48213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_64,c_48163])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:52:11 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 18.10/10.43  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.10/10.43  
% 18.10/10.43  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.10/10.43  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_4
% 18.10/10.43  
% 18.10/10.43  %Foreground sorts:
% 18.10/10.43  
% 18.10/10.43  
% 18.10/10.43  %Background operators:
% 18.10/10.43  
% 18.10/10.43  
% 18.10/10.43  %Foreground operators:
% 18.10/10.43  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 18.10/10.43  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 18.10/10.43  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 18.10/10.43  tff(k1_tarski, type, k1_tarski: $i > $i).
% 18.10/10.43  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 18.10/10.43  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 18.10/10.43  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 18.10/10.43  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 18.10/10.43  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 18.10/10.43  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 18.10/10.43  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 18.10/10.43  tff('#skF_5', type, '#skF_5': $i).
% 18.10/10.43  tff('#skF_6', type, '#skF_6': $i).
% 18.10/10.43  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 18.10/10.43  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 18.10/10.43  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 18.10/10.43  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 18.10/10.43  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 18.10/10.43  tff(k3_tarski, type, k3_tarski: $i > $i).
% 18.10/10.43  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 18.10/10.43  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 18.10/10.43  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 18.10/10.43  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 18.10/10.43  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 18.10/10.43  
% 18.10/10.44  tff(f_39, axiom, (![A, B]: (k4_xboole_0(k2_xboole_0(A, B), B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t40_xboole_1)).
% 18.10/10.44  tff(f_78, negated_conjecture, ~(![A, B]: (~r2_hidden(A, B) => (k4_xboole_0(k2_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t141_zfmisc_1)).
% 18.10/10.44  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 18.10/10.44  tff(f_56, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 18.10/10.44  tff(c_22, plain, (![A_9, B_10]: (k4_xboole_0(k2_xboole_0(A_9, B_10), B_10)=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 18.10/10.44  tff(c_62, plain, (k4_xboole_0(k2_xboole_0('#skF_6', k1_tarski('#skF_5')), k1_tarski('#skF_5'))!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_78])).
% 18.10/10.44  tff(c_65, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_22, c_62])).
% 18.10/10.44  tff(c_64, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_78])).
% 18.10/10.44  tff(c_18, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), C_3) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.10/10.44  tff(c_2900, plain, (![A_3473, B_3474, C_3475]: (~r2_hidden('#skF_1'(A_3473, B_3474, C_3475), C_3475) | r2_hidden('#skF_2'(A_3473, B_3474, C_3475), C_3475) | k4_xboole_0(A_3473, B_3474)=C_3475)), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.10/10.44  tff(c_2910, plain, (![A_1, B_2]: (r2_hidden('#skF_2'(A_1, B_2, A_1), A_1) | k4_xboole_0(A_1, B_2)=A_1)), inference(resolution, [status(thm)], [c_18, c_2900])).
% 18.10/10.44  tff(c_12, plain, (![A_1, B_2, C_3]: (r2_hidden('#skF_1'(A_1, B_2, C_3), A_1) | r2_hidden('#skF_2'(A_1, B_2, C_3), B_2) | ~r2_hidden('#skF_2'(A_1, B_2, C_3), A_1) | k4_xboole_0(A_1, B_2)=C_3)), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.10/10.44  tff(c_3699, plain, (![A_4386, B_4387, C_4388]: (~r2_hidden('#skF_1'(A_4386, B_4387, C_4388), C_4388) | r2_hidden('#skF_2'(A_4386, B_4387, C_4388), B_4387) | ~r2_hidden('#skF_2'(A_4386, B_4387, C_4388), A_4386) | k4_xboole_0(A_4386, B_4387)=C_4388)), inference(cnfTransformation, [status(thm)], [f_35])).
% 18.10/10.44  tff(c_8876, plain, (![A_7786, B_7787]: (r2_hidden('#skF_2'(A_7786, B_7787, A_7786), B_7787) | ~r2_hidden('#skF_2'(A_7786, B_7787, A_7786), A_7786) | k4_xboole_0(A_7786, B_7787)=A_7786)), inference(resolution, [status(thm)], [c_12, c_3699])).
% 18.10/10.44  tff(c_23004, plain, (![A_11751, B_11752]: (r2_hidden('#skF_2'(A_11751, B_11752, A_11751), B_11752) | k4_xboole_0(A_11751, B_11752)=A_11751)), inference(resolution, [status(thm)], [c_2910, c_8876])).
% 18.10/10.44  tff(c_34, plain, (![C_24, A_20]: (C_24=A_20 | ~r2_hidden(C_24, k1_tarski(A_20)))), inference(cnfTransformation, [status(thm)], [f_56])).
% 18.10/10.44  tff(c_47808, plain, (![A_13719, A_13720]: ('#skF_2'(A_13719, k1_tarski(A_13720), A_13719)=A_13720 | k4_xboole_0(A_13719, k1_tarski(A_13720))=A_13719)), inference(resolution, [status(thm)], [c_23004, c_34])).
% 18.10/10.44  tff(c_48148, plain, ('#skF_2'('#skF_6', k1_tarski('#skF_5'), '#skF_6')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_47808, c_65])).
% 18.10/10.44  tff(c_48163, plain, (r2_hidden('#skF_5', '#skF_6') | k4_xboole_0('#skF_6', k1_tarski('#skF_5'))='#skF_6'), inference(superposition, [status(thm), theory('equality')], [c_48148, c_2910])).
% 18.10/10.44  tff(c_48213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_64, c_48163])).
% 18.10/10.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 18.10/10.44  
% 18.10/10.44  Inference rules
% 18.10/10.44  ----------------------
% 18.10/10.44  #Ref     : 0
% 18.10/10.44  #Sup     : 11993
% 18.10/10.44  #Fact    : 4
% 18.10/10.44  #Define  : 0
% 18.10/10.44  #Split   : 3
% 18.10/10.44  #Chain   : 0
% 18.10/10.44  #Close   : 0
% 18.10/10.44  
% 18.10/10.44  Ordering : KBO
% 18.10/10.44  
% 18.10/10.44  Simplification rules
% 18.10/10.44  ----------------------
% 18.10/10.44  #Subsume      : 952
% 18.10/10.44  #Demod        : 16638
% 18.10/10.44  #Tautology    : 4600
% 18.10/10.44  #SimpNegUnit  : 71
% 18.10/10.44  #BackRed      : 35
% 18.10/10.44  
% 18.10/10.44  #Partial instantiations: 4800
% 18.10/10.44  #Strategies tried      : 1
% 18.10/10.44  
% 18.10/10.44  Timing (in seconds)
% 18.10/10.44  ----------------------
% 18.10/10.44  Preprocessing        : 0.36
% 18.10/10.44  Parsing              : 0.19
% 18.10/10.44  CNF conversion       : 0.03
% 18.10/10.44  Main loop            : 9.29
% 18.10/10.44  Inferencing          : 1.46
% 18.10/10.44  Reduction            : 6.12
% 18.10/10.44  Demodulation         : 5.72
% 18.10/10.44  BG Simplification    : 0.21
% 18.10/10.44  Subsumption          : 1.18
% 18.10/10.44  Abstraction          : 0.38
% 18.10/10.44  MUC search           : 0.00
% 18.10/10.44  Cooper               : 0.00
% 18.10/10.44  Total                : 9.67
% 18.10/10.44  Index Insertion      : 0.00
% 18.10/10.44  Index Deletion       : 0.00
% 18.10/10.44  Index Matching       : 0.00
% 18.10/10.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:52 EST 2020

% Result     : Theorem 2.30s
% Output     : CNFRefutation 2.30s
% Verified   : 
% Statistics : Number of formulae       :   47 (  50 expanded)
%              Number of leaves         :   31 (  33 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  44 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_86,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_64,plain,(
    k2_xboole_0(k2_tarski('#skF_5','#skF_6'),'#skF_7') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_30,plain,(
    ! [A_19,B_20] : r1_tarski(A_19,k2_xboole_0(A_19,B_20)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_92,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_30])).

tff(c_256,plain,(
    ! [A_82,B_83] :
      ( r2_hidden('#skF_2'(A_82,B_83),A_82)
      | r1_tarski(A_82,B_83) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_262,plain,(
    ! [A_84,B_85] :
      ( ~ v1_xboole_0(A_84)
      | r1_tarski(A_84,B_85) ) ),
    inference(resolution,[status(thm)],[c_256,c_2])).

tff(c_14,plain,(
    ! [B_11,A_10] :
      ( B_11 = A_10
      | ~ r1_tarski(B_11,A_10)
      | ~ r1_tarski(A_10,B_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_343,plain,(
    ! [B_94,A_95] :
      ( B_94 = A_95
      | ~ r1_tarski(B_94,A_95)
      | ~ v1_xboole_0(A_95) ) ),
    inference(resolution,[status(thm)],[c_262,c_14])).

tff(c_352,plain,
    ( k2_tarski('#skF_5','#skF_6') = k1_xboole_0
    | ~ v1_xboole_0(k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_92,c_343])).

tff(c_363,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_352])).

tff(c_38,plain,(
    ! [D_31,A_26] : r2_hidden(D_31,k2_tarski(A_26,D_31)) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_79,plain,(
    ! [B_56,A_57] :
      ( ~ r2_hidden(B_56,A_57)
      | ~ v1_xboole_0(A_57) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_86,plain,(
    ! [A_26,D_31] : ~ v1_xboole_0(k2_tarski(A_26,D_31)) ),
    inference(resolution,[status(thm)],[c_38,c_79])).

tff(c_379,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_363,c_86])).

tff(c_390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_379])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n024.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 10:01:36 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.30/1.60  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.60  
% 2.30/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.60  %$ r2_hidden > r1_tarski > v1_xboole_0 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 2.30/1.60  
% 2.30/1.60  %Foreground sorts:
% 2.30/1.60  
% 2.30/1.60  
% 2.30/1.60  %Background operators:
% 2.30/1.60  
% 2.30/1.60  
% 2.30/1.60  %Foreground operators:
% 2.30/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.30/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.30/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.30/1.60  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.30/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.30/1.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.30/1.60  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.30/1.60  tff('#skF_7', type, '#skF_7': $i).
% 2.30/1.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.30/1.60  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.30/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.30/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.30/1.60  tff('#skF_5', type, '#skF_5': $i).
% 2.30/1.60  tff('#skF_6', type, '#skF_6': $i).
% 2.30/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.30/1.60  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.30/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.30/1.60  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.30/1.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.30/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.30/1.60  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.30/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.30/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.30/1.60  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.30/1.60  
% 2.30/1.61  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.30/1.61  tff(f_86, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.30/1.61  tff(f_59, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.30/1.61  tff(f_38, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 2.30/1.61  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.30/1.61  tff(f_45, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.30/1.61  tff(f_72, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 2.30/1.61  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.30/1.61  tff(c_64, plain, (k2_xboole_0(k2_tarski('#skF_5', '#skF_6'), '#skF_7')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.30/1.61  tff(c_30, plain, (![A_19, B_20]: (r1_tarski(A_19, k2_xboole_0(A_19, B_20)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.30/1.61  tff(c_92, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_64, c_30])).
% 2.30/1.61  tff(c_256, plain, (![A_82, B_83]: (r2_hidden('#skF_2'(A_82, B_83), A_82) | r1_tarski(A_82, B_83))), inference(cnfTransformation, [status(thm)], [f_38])).
% 2.30/1.61  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.61  tff(c_262, plain, (![A_84, B_85]: (~v1_xboole_0(A_84) | r1_tarski(A_84, B_85))), inference(resolution, [status(thm)], [c_256, c_2])).
% 2.30/1.61  tff(c_14, plain, (![B_11, A_10]: (B_11=A_10 | ~r1_tarski(B_11, A_10) | ~r1_tarski(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.30/1.61  tff(c_343, plain, (![B_94, A_95]: (B_94=A_95 | ~r1_tarski(B_94, A_95) | ~v1_xboole_0(A_95))), inference(resolution, [status(thm)], [c_262, c_14])).
% 2.30/1.61  tff(c_352, plain, (k2_tarski('#skF_5', '#skF_6')=k1_xboole_0 | ~v1_xboole_0(k1_xboole_0)), inference(resolution, [status(thm)], [c_92, c_343])).
% 2.30/1.61  tff(c_363, plain, (k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_12, c_352])).
% 2.30/1.61  tff(c_38, plain, (![D_31, A_26]: (r2_hidden(D_31, k2_tarski(A_26, D_31)))), inference(cnfTransformation, [status(thm)], [f_72])).
% 2.30/1.61  tff(c_79, plain, (![B_56, A_57]: (~r2_hidden(B_56, A_57) | ~v1_xboole_0(A_57))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.30/1.61  tff(c_86, plain, (![A_26, D_31]: (~v1_xboole_0(k2_tarski(A_26, D_31)))), inference(resolution, [status(thm)], [c_38, c_79])).
% 2.30/1.61  tff(c_379, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_363, c_86])).
% 2.30/1.61  tff(c_390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_379])).
% 2.30/1.61  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.30/1.61  
% 2.30/1.61  Inference rules
% 2.30/1.61  ----------------------
% 2.30/1.61  #Ref     : 0
% 2.30/1.61  #Sup     : 78
% 2.30/1.61  #Fact    : 0
% 2.30/1.61  #Define  : 0
% 2.30/1.61  #Split   : 0
% 2.30/1.61  #Chain   : 0
% 2.30/1.61  #Close   : 0
% 2.30/1.61  
% 2.30/1.61  Ordering : KBO
% 2.30/1.61  
% 2.30/1.61  Simplification rules
% 2.30/1.61  ----------------------
% 2.30/1.61  #Subsume      : 1
% 2.30/1.61  #Demod        : 21
% 2.30/1.61  #Tautology    : 52
% 2.30/1.61  #SimpNegUnit  : 0
% 2.30/1.61  #BackRed      : 4
% 2.30/1.61  
% 2.30/1.61  #Partial instantiations: 0
% 2.30/1.61  #Strategies tried      : 1
% 2.30/1.61  
% 2.30/1.61  Timing (in seconds)
% 2.30/1.61  ----------------------
% 2.30/1.61  Preprocessing        : 0.51
% 2.30/1.61  Parsing              : 0.26
% 2.30/1.61  CNF conversion       : 0.04
% 2.30/1.61  Main loop            : 0.20
% 2.30/1.61  Inferencing          : 0.07
% 2.30/1.61  Reduction            : 0.07
% 2.30/1.62  Demodulation         : 0.05
% 2.30/1.62  BG Simplification    : 0.02
% 2.30/1.62  Subsumption          : 0.03
% 2.30/1.62  Abstraction          : 0.01
% 2.30/1.62  MUC search           : 0.00
% 2.30/1.62  Cooper               : 0.00
% 2.30/1.62  Total                : 0.74
% 2.30/1.62  Index Insertion      : 0.00
% 2.30/1.62  Index Deletion       : 0.00
% 2.30/1.62  Index Matching       : 0.00
% 2.30/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------

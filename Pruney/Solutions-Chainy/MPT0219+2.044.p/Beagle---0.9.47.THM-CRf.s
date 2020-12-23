%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:55 EST 2020

% Result     : Theorem 6.68s
% Output     : CNFRefutation 6.68s
% Verified   : 
% Statistics : Number of formulae       :   41 (  43 expanded)
%              Number of leaves         :   26 (  28 expanded)
%              Depth                    :    8
%              Number of atoms          :   44 (  49 expanded)
%              Number of equality atoms :   10 (  12 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(f_87,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_70,plain,(
    '#skF_5' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_8,plain,(
    ! [A_3,B_4] :
      ( r2_hidden('#skF_1'(A_3,B_4),A_3)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_72,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_5')) = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_10,plain,(
    ! [D_13,A_8,B_9] :
      ( r2_hidden(D_13,k4_xboole_0(A_8,B_9))
      | r2_hidden(D_13,B_9)
      | ~ r2_hidden(D_13,A_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_58,plain,(
    ! [A_29,B_30] : k5_xboole_0(A_29,k4_xboole_0(B_30,A_29)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1374,plain,(
    ! [A_121,B_122,C_123] :
      ( r2_hidden(A_121,B_122)
      | ~ r2_hidden(A_121,C_123)
      | r2_hidden(A_121,k5_xboole_0(B_122,C_123)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_5296,plain,(
    ! [A_251,A_252,B_253] :
      ( r2_hidden(A_251,A_252)
      | ~ r2_hidden(A_251,k4_xboole_0(B_253,A_252))
      | r2_hidden(A_251,k2_xboole_0(A_252,B_253)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_1374])).

tff(c_8870,plain,(
    ! [D_334,B_335,A_336] :
      ( r2_hidden(D_334,k2_xboole_0(B_335,A_336))
      | r2_hidden(D_334,B_335)
      | ~ r2_hidden(D_334,A_336) ) ),
    inference(resolution,[status(thm)],[c_10,c_5296])).

tff(c_9066,plain,(
    ! [D_340] :
      ( r2_hidden(D_340,k1_tarski('#skF_4'))
      | r2_hidden(D_340,k1_tarski('#skF_4'))
      | ~ r2_hidden(D_340,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_8870])).

tff(c_9700,plain,(
    ! [B_363] :
      ( r2_hidden('#skF_1'(k1_tarski('#skF_5'),B_363),k1_tarski('#skF_4'))
      | r1_tarski(k1_tarski('#skF_5'),B_363) ) ),
    inference(resolution,[status(thm)],[c_8,c_9066])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( ~ r2_hidden('#skF_1'(A_3,B_4),B_4)
      | r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_9712,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_9700,c_6])).

tff(c_68,plain,(
    ! [B_42,A_41] :
      ( B_42 = A_41
      | ~ r1_tarski(k1_tarski(A_41),k1_tarski(B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_9719,plain,(
    '#skF_5' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_9712,c_68])).

tff(c_9731,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_70,c_9719])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:55:46 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.68/2.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.68/2.50  
% 6.68/2.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.68/2.50  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 6.68/2.50  
% 6.68/2.50  %Foreground sorts:
% 6.68/2.50  
% 6.68/2.50  
% 6.68/2.50  %Background operators:
% 6.68/2.50  
% 6.68/2.50  
% 6.68/2.50  %Foreground operators:
% 6.68/2.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.68/2.50  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.68/2.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.68/2.50  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.68/2.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.68/2.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.68/2.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.68/2.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.68/2.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.68/2.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.68/2.50  tff('#skF_5', type, '#skF_5': $i).
% 6.68/2.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.68/2.50  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 6.68/2.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.68/2.50  tff('#skF_4', type, '#skF_4': $i).
% 6.68/2.50  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.68/2.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.68/2.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.68/2.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.68/2.50  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 6.68/2.50  
% 6.68/2.51  tff(f_92, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 6.68/2.51  tff(f_34, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 6.68/2.51  tff(f_44, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 6.68/2.51  tff(f_75, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.68/2.51  tff(f_51, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 6.68/2.51  tff(f_87, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 6.68/2.51  tff(c_70, plain, ('#skF_5'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.68/2.51  tff(c_8, plain, (![A_3, B_4]: (r2_hidden('#skF_1'(A_3, B_4), A_3) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.68/2.51  tff(c_72, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_5'))=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 6.68/2.51  tff(c_10, plain, (![D_13, A_8, B_9]: (r2_hidden(D_13, k4_xboole_0(A_8, B_9)) | r2_hidden(D_13, B_9) | ~r2_hidden(D_13, A_8))), inference(cnfTransformation, [status(thm)], [f_44])).
% 6.68/2.51  tff(c_58, plain, (![A_29, B_30]: (k5_xboole_0(A_29, k4_xboole_0(B_30, A_29))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_75])).
% 6.68/2.51  tff(c_1374, plain, (![A_121, B_122, C_123]: (r2_hidden(A_121, B_122) | ~r2_hidden(A_121, C_123) | r2_hidden(A_121, k5_xboole_0(B_122, C_123)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.68/2.51  tff(c_5296, plain, (![A_251, A_252, B_253]: (r2_hidden(A_251, A_252) | ~r2_hidden(A_251, k4_xboole_0(B_253, A_252)) | r2_hidden(A_251, k2_xboole_0(A_252, B_253)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_1374])).
% 6.68/2.51  tff(c_8870, plain, (![D_334, B_335, A_336]: (r2_hidden(D_334, k2_xboole_0(B_335, A_336)) | r2_hidden(D_334, B_335) | ~r2_hidden(D_334, A_336))), inference(resolution, [status(thm)], [c_10, c_5296])).
% 6.68/2.51  tff(c_9066, plain, (![D_340]: (r2_hidden(D_340, k1_tarski('#skF_4')) | r2_hidden(D_340, k1_tarski('#skF_4')) | ~r2_hidden(D_340, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_72, c_8870])).
% 6.68/2.51  tff(c_9700, plain, (![B_363]: (r2_hidden('#skF_1'(k1_tarski('#skF_5'), B_363), k1_tarski('#skF_4')) | r1_tarski(k1_tarski('#skF_5'), B_363))), inference(resolution, [status(thm)], [c_8, c_9066])).
% 6.68/2.51  tff(c_6, plain, (![A_3, B_4]: (~r2_hidden('#skF_1'(A_3, B_4), B_4) | r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_34])).
% 6.68/2.51  tff(c_9712, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_9700, c_6])).
% 6.68/2.51  tff(c_68, plain, (![B_42, A_41]: (B_42=A_41 | ~r1_tarski(k1_tarski(A_41), k1_tarski(B_42)))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.68/2.51  tff(c_9719, plain, ('#skF_5'='#skF_4'), inference(resolution, [status(thm)], [c_9712, c_68])).
% 6.68/2.51  tff(c_9731, plain, $false, inference(negUnitSimplification, [status(thm)], [c_70, c_9719])).
% 6.68/2.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.68/2.51  
% 6.68/2.51  Inference rules
% 6.68/2.51  ----------------------
% 6.68/2.51  #Ref     : 0
% 6.68/2.51  #Sup     : 2357
% 6.68/2.51  #Fact    : 2
% 6.68/2.51  #Define  : 0
% 6.68/2.51  #Split   : 0
% 6.68/2.51  #Chain   : 0
% 6.68/2.51  #Close   : 0
% 6.68/2.51  
% 6.68/2.51  Ordering : KBO
% 6.68/2.51  
% 6.68/2.51  Simplification rules
% 6.68/2.51  ----------------------
% 6.68/2.51  #Subsume      : 441
% 6.68/2.51  #Demod        : 2319
% 6.68/2.51  #Tautology    : 1308
% 6.68/2.51  #SimpNegUnit  : 1
% 6.68/2.51  #BackRed      : 9
% 6.68/2.51  
% 6.68/2.51  #Partial instantiations: 0
% 6.68/2.51  #Strategies tried      : 1
% 6.68/2.51  
% 6.68/2.51  Timing (in seconds)
% 6.68/2.51  ----------------------
% 6.68/2.51  Preprocessing        : 0.35
% 6.68/2.51  Parsing              : 0.17
% 6.68/2.51  CNF conversion       : 0.03
% 6.68/2.51  Main loop            : 1.40
% 6.68/2.51  Inferencing          : 0.40
% 6.68/2.51  Reduction            : 0.61
% 6.68/2.51  Demodulation         : 0.51
% 6.68/2.51  BG Simplification    : 0.05
% 6.68/2.52  Subsumption          : 0.26
% 6.68/2.52  Abstraction          : 0.06
% 6.68/2.52  MUC search           : 0.00
% 6.68/2.52  Cooper               : 0.00
% 6.68/2.52  Total                : 1.77
% 6.68/2.52  Index Insertion      : 0.00
% 6.68/2.52  Index Deletion       : 0.00
% 6.68/2.52  Index Matching       : 0.00
% 6.68/2.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:56 EST 2020

% Result     : Theorem 6.75s
% Output     : CNFRefutation 7.12s
% Verified   : 
% Statistics : Number of formulae       :   46 (  48 expanded)
%              Number of leaves         :   32 (  34 expanded)
%              Depth                    :    8
%              Number of atoms          :   40 (  45 expanded)
%              Number of equality atoms :   12 (  16 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_11 > #skF_4 > #skF_8 > #skF_10 > #skF_2 > #skF_7 > #skF_3 > #skF_9 > #skF_5 > #skF_12

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff(f_105,negated_conjecture,(
    ~ ! [A,B] :
        ( k2_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_zfmisc_1)).

tff(f_92,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_70,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k5_xboole_0(B,C))
    <=> ~ ( r2_hidden(A,B)
        <=> r2_hidden(A,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_0)).

tff(c_112,plain,(
    '#skF_11' != '#skF_12' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_94,plain,(
    ! [C_39] : r2_hidden(C_39,k1_tarski(C_39)) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_114,plain,(
    k2_xboole_0(k1_tarski('#skF_11'),k1_tarski('#skF_12')) = k1_tarski('#skF_11') ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_22,plain,(
    ! [D_14,A_9,B_10] :
      ( r2_hidden(D_14,k4_xboole_0(A_9,B_10))
      | r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,A_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_66,plain,(
    ! [A_26,B_27] : k5_xboole_0(A_26,k4_xboole_0(B_27,A_26)) = k2_xboole_0(A_26,B_27) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_441,plain,(
    ! [A_103,B_104,C_105] :
      ( r2_hidden(A_103,B_104)
      | ~ r2_hidden(A_103,C_105)
      | r2_hidden(A_103,k5_xboole_0(B_104,C_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_8743,plain,(
    ! [A_392,A_393,B_394] :
      ( r2_hidden(A_392,A_393)
      | ~ r2_hidden(A_392,k4_xboole_0(B_394,A_393))
      | r2_hidden(A_392,k2_xboole_0(A_393,B_394)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_441])).

tff(c_9026,plain,(
    ! [D_395,B_396,A_397] :
      ( r2_hidden(D_395,k2_xboole_0(B_396,A_397))
      | r2_hidden(D_395,B_396)
      | ~ r2_hidden(D_395,A_397) ) ),
    inference(resolution,[status(thm)],[c_22,c_8743])).

tff(c_9125,plain,(
    ! [D_395] :
      ( r2_hidden(D_395,k1_tarski('#skF_11'))
      | r2_hidden(D_395,k1_tarski('#skF_11'))
      | ~ r2_hidden(D_395,k1_tarski('#skF_12')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_114,c_9026])).

tff(c_9223,plain,(
    ! [D_399] :
      ( ~ r2_hidden(D_399,k1_tarski('#skF_12'))
      | r2_hidden(D_399,k1_tarski('#skF_11')) ) ),
    inference(factorization,[status(thm),theory(equality)],[c_9125])).

tff(c_92,plain,(
    ! [C_39,A_35] :
      ( C_39 = A_35
      | ~ r2_hidden(C_39,k1_tarski(A_35)) ) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_9310,plain,(
    ! [D_400] :
      ( D_400 = '#skF_11'
      | ~ r2_hidden(D_400,k1_tarski('#skF_12')) ) ),
    inference(resolution,[status(thm)],[c_9223,c_92])).

tff(c_9518,plain,(
    '#skF_11' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_94,c_9310])).

tff(c_9579,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_112,c_9518])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n024.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 16:55:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.75/2.56  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/2.56  
% 7.12/2.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/2.56  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_1 > #skF_11 > #skF_4 > #skF_8 > #skF_10 > #skF_2 > #skF_7 > #skF_3 > #skF_9 > #skF_5 > #skF_12
% 7.12/2.56  
% 7.12/2.56  %Foreground sorts:
% 7.12/2.56  
% 7.12/2.56  
% 7.12/2.56  %Background operators:
% 7.12/2.56  
% 7.12/2.56  
% 7.12/2.56  %Foreground operators:
% 7.12/2.56  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 7.12/2.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 7.12/2.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.12/2.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.12/2.56  tff('#skF_11', type, '#skF_11': $i).
% 7.12/2.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.12/2.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.12/2.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.12/2.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.12/2.56  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 7.12/2.56  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.12/2.56  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.12/2.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.12/2.56  tff('#skF_8', type, '#skF_8': ($i * $i * $i * $i) > $i).
% 7.12/2.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.12/2.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.12/2.56  tff('#skF_10', type, '#skF_10': ($i * $i) > $i).
% 7.12/2.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 7.12/2.56  tff('#skF_7', type, '#skF_7': ($i * $i * $i * $i) > $i).
% 7.12/2.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.12/2.56  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 7.12/2.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.12/2.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.12/2.56  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.12/2.56  tff('#skF_9', type, '#skF_9': ($i * $i) > $i).
% 7.12/2.56  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 7.12/2.56  tff('#skF_12', type, '#skF_12': $i).
% 7.12/2.56  
% 7.12/2.57  tff(f_105, negated_conjecture, ~(![A, B]: ((k2_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_zfmisc_1)).
% 7.12/2.57  tff(f_92, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 7.12/2.57  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 7.12/2.57  tff(f_70, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.12/2.57  tff(f_53, axiom, (![A, B, C]: (r2_hidden(A, k5_xboole_0(B, C)) <=> ~(r2_hidden(A, B) <=> r2_hidden(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_0)).
% 7.12/2.57  tff(c_112, plain, ('#skF_11'!='#skF_12'), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.12/2.57  tff(c_94, plain, (![C_39]: (r2_hidden(C_39, k1_tarski(C_39)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.12/2.57  tff(c_114, plain, (k2_xboole_0(k1_tarski('#skF_11'), k1_tarski('#skF_12'))=k1_tarski('#skF_11')), inference(cnfTransformation, [status(thm)], [f_105])).
% 7.12/2.57  tff(c_22, plain, (![D_14, A_9, B_10]: (r2_hidden(D_14, k4_xboole_0(A_9, B_10)) | r2_hidden(D_14, B_10) | ~r2_hidden(D_14, A_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 7.12/2.57  tff(c_66, plain, (![A_26, B_27]: (k5_xboole_0(A_26, k4_xboole_0(B_27, A_26))=k2_xboole_0(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.12/2.57  tff(c_441, plain, (![A_103, B_104, C_105]: (r2_hidden(A_103, B_104) | ~r2_hidden(A_103, C_105) | r2_hidden(A_103, k5_xboole_0(B_104, C_105)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.12/2.57  tff(c_8743, plain, (![A_392, A_393, B_394]: (r2_hidden(A_392, A_393) | ~r2_hidden(A_392, k4_xboole_0(B_394, A_393)) | r2_hidden(A_392, k2_xboole_0(A_393, B_394)))), inference(superposition, [status(thm), theory('equality')], [c_66, c_441])).
% 7.12/2.57  tff(c_9026, plain, (![D_395, B_396, A_397]: (r2_hidden(D_395, k2_xboole_0(B_396, A_397)) | r2_hidden(D_395, B_396) | ~r2_hidden(D_395, A_397))), inference(resolution, [status(thm)], [c_22, c_8743])).
% 7.12/2.57  tff(c_9125, plain, (![D_395]: (r2_hidden(D_395, k1_tarski('#skF_11')) | r2_hidden(D_395, k1_tarski('#skF_11')) | ~r2_hidden(D_395, k1_tarski('#skF_12')))), inference(superposition, [status(thm), theory('equality')], [c_114, c_9026])).
% 7.12/2.57  tff(c_9223, plain, (![D_399]: (~r2_hidden(D_399, k1_tarski('#skF_12')) | r2_hidden(D_399, k1_tarski('#skF_11')))), inference(factorization, [status(thm), theory('equality')], [c_9125])).
% 7.12/2.57  tff(c_92, plain, (![C_39, A_35]: (C_39=A_35 | ~r2_hidden(C_39, k1_tarski(A_35)))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.12/2.57  tff(c_9310, plain, (![D_400]: (D_400='#skF_11' | ~r2_hidden(D_400, k1_tarski('#skF_12')))), inference(resolution, [status(thm)], [c_9223, c_92])).
% 7.12/2.57  tff(c_9518, plain, ('#skF_11'='#skF_12'), inference(resolution, [status(thm)], [c_94, c_9310])).
% 7.12/2.57  tff(c_9579, plain, $false, inference(negUnitSimplification, [status(thm)], [c_112, c_9518])).
% 7.12/2.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.12/2.57  
% 7.12/2.57  Inference rules
% 7.12/2.57  ----------------------
% 7.12/2.57  #Ref     : 0
% 7.12/2.57  #Sup     : 2033
% 7.12/2.57  #Fact    : 2
% 7.12/2.57  #Define  : 0
% 7.12/2.57  #Split   : 0
% 7.12/2.57  #Chain   : 0
% 7.12/2.57  #Close   : 0
% 7.12/2.57  
% 7.12/2.57  Ordering : KBO
% 7.12/2.57  
% 7.12/2.57  Simplification rules
% 7.12/2.57  ----------------------
% 7.12/2.57  #Subsume      : 306
% 7.12/2.57  #Demod        : 796
% 7.12/2.57  #Tautology    : 400
% 7.12/2.57  #SimpNegUnit  : 139
% 7.12/2.57  #BackRed      : 6
% 7.12/2.57  
% 7.12/2.57  #Partial instantiations: 0
% 7.12/2.57  #Strategies tried      : 1
% 7.12/2.57  
% 7.12/2.57  Timing (in seconds)
% 7.12/2.57  ----------------------
% 7.12/2.57  Preprocessing        : 0.34
% 7.12/2.57  Parsing              : 0.16
% 7.12/2.57  CNF conversion       : 0.03
% 7.12/2.57  Main loop            : 1.43
% 7.12/2.57  Inferencing          : 0.45
% 7.12/2.57  Reduction            : 0.49
% 7.12/2.57  Demodulation         : 0.36
% 7.12/2.57  BG Simplification    : 0.07
% 7.12/2.57  Subsumption          : 0.31
% 7.12/2.57  Abstraction          : 0.08
% 7.12/2.57  MUC search           : 0.00
% 7.12/2.57  Cooper               : 0.00
% 7.12/2.57  Total                : 1.80
% 7.12/2.57  Index Insertion      : 0.00
% 7.12/2.57  Index Deletion       : 0.00
% 7.12/2.57  Index Matching       : 0.00
% 7.12/2.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------

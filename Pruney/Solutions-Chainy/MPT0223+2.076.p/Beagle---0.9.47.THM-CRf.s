%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:26 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :   39 (  42 expanded)
%              Number of leaves         :   26 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   33 (  42 expanded)
%              Number of equality atoms :   12 (  17 expanded)
%              Maximal formula depth    :   10 (   5 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_71,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_52,axiom,(
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

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(c_50,plain,(
    '#skF_7' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_26,plain,(
    ! [C_15] : r2_hidden(C_15,k1_tarski(C_15)) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_52,plain,(
    k3_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_476,plain,(
    ! [D_90,A_91,B_92] :
      ( r2_hidden(D_90,k4_xboole_0(A_91,B_92))
      | r2_hidden(D_90,B_92)
      | ~ r2_hidden(D_90,A_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_22,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_117,plain,(
    ! [D_54,B_55,A_56] :
      ( ~ r2_hidden(D_54,B_55)
      | ~ r2_hidden(D_54,k4_xboole_0(A_56,B_55)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_120,plain,(
    ! [D_54,A_9,B_10] :
      ( ~ r2_hidden(D_54,k4_xboole_0(A_9,B_10))
      | ~ r2_hidden(D_54,k3_xboole_0(A_9,B_10)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_117])).

tff(c_1444,plain,(
    ! [D_127,A_128,B_129] :
      ( ~ r2_hidden(D_127,k3_xboole_0(A_128,B_129))
      | r2_hidden(D_127,B_129)
      | ~ r2_hidden(D_127,A_128) ) ),
    inference(resolution,[status(thm)],[c_476,c_120])).

tff(c_1617,plain,(
    ! [D_140] :
      ( ~ r2_hidden(D_140,k1_tarski('#skF_6'))
      | r2_hidden(D_140,k1_tarski('#skF_7'))
      | ~ r2_hidden(D_140,k1_tarski('#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1444])).

tff(c_24,plain,(
    ! [C_15,A_11] :
      ( C_15 = A_11
      | ~ r2_hidden(C_15,k1_tarski(A_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_1632,plain,(
    ! [D_141] :
      ( D_141 = '#skF_7'
      | ~ r2_hidden(D_141,k1_tarski('#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_1617,c_24])).

tff(c_1664,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_26,c_1632])).

tff(c_1677,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_1664])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.33  % Computer   : n018.cluster.edu
% 0.11/0.33  % Model      : x86_64 x86_64
% 0.11/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.33  % Memory     : 8042.1875MB
% 0.11/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.33  % CPULimit   : 60
% 0.11/0.33  % DateTime   : Tue Dec  1 10:57:56 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.41/1.55  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.56  
% 3.41/1.56  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.56  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_6 > #skF_2 > #skF_3 > #skF_5 > #skF_4
% 3.41/1.56  
% 3.41/1.56  %Foreground sorts:
% 3.41/1.56  
% 3.41/1.56  
% 3.41/1.56  %Background operators:
% 3.41/1.56  
% 3.41/1.56  
% 3.41/1.56  %Foreground operators:
% 3.41/1.56  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.41/1.56  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.56  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.41/1.56  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.41/1.56  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.41/1.56  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.41/1.56  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.41/1.56  tff('#skF_7', type, '#skF_7': $i).
% 3.41/1.56  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.41/1.56  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.41/1.56  tff('#skF_6', type, '#skF_6': $i).
% 3.41/1.56  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.41/1.56  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.41/1.56  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.41/1.56  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.41/1.56  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.56  tff('#skF_3', type, '#skF_3': $i > $i).
% 3.41/1.56  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.56  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.41/1.56  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.41/1.56  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.41/1.56  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.41/1.56  
% 3.41/1.57  tff(f_71, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 3.41/1.57  tff(f_52, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.41/1.57  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.41/1.57  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.41/1.57  tff(c_50, plain, ('#skF_7'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.41/1.57  tff(c_26, plain, (![C_15]: (r2_hidden(C_15, k1_tarski(C_15)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.41/1.57  tff(c_52, plain, (k3_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_71])).
% 3.41/1.57  tff(c_476, plain, (![D_90, A_91, B_92]: (r2_hidden(D_90, k4_xboole_0(A_91, B_92)) | r2_hidden(D_90, B_92) | ~r2_hidden(D_90, A_91))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.41/1.57  tff(c_22, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.41/1.57  tff(c_117, plain, (![D_54, B_55, A_56]: (~r2_hidden(D_54, B_55) | ~r2_hidden(D_54, k4_xboole_0(A_56, B_55)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.41/1.57  tff(c_120, plain, (![D_54, A_9, B_10]: (~r2_hidden(D_54, k4_xboole_0(A_9, B_10)) | ~r2_hidden(D_54, k3_xboole_0(A_9, B_10)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_117])).
% 3.41/1.57  tff(c_1444, plain, (![D_127, A_128, B_129]: (~r2_hidden(D_127, k3_xboole_0(A_128, B_129)) | r2_hidden(D_127, B_129) | ~r2_hidden(D_127, A_128))), inference(resolution, [status(thm)], [c_476, c_120])).
% 3.41/1.57  tff(c_1617, plain, (![D_140]: (~r2_hidden(D_140, k1_tarski('#skF_6')) | r2_hidden(D_140, k1_tarski('#skF_7')) | ~r2_hidden(D_140, k1_tarski('#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1444])).
% 3.41/1.57  tff(c_24, plain, (![C_15, A_11]: (C_15=A_11 | ~r2_hidden(C_15, k1_tarski(A_11)))), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.41/1.57  tff(c_1632, plain, (![D_141]: (D_141='#skF_7' | ~r2_hidden(D_141, k1_tarski('#skF_6')))), inference(resolution, [status(thm)], [c_1617, c_24])).
% 3.41/1.57  tff(c_1664, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_26, c_1632])).
% 3.41/1.57  tff(c_1677, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_1664])).
% 3.41/1.57  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.41/1.57  
% 3.41/1.57  Inference rules
% 3.41/1.57  ----------------------
% 3.41/1.57  #Ref     : 0
% 3.41/1.57  #Sup     : 372
% 3.41/1.57  #Fact    : 0
% 3.41/1.57  #Define  : 0
% 3.41/1.57  #Split   : 0
% 3.41/1.57  #Chain   : 0
% 3.41/1.57  #Close   : 0
% 3.41/1.57  
% 3.41/1.57  Ordering : KBO
% 3.41/1.57  
% 3.41/1.57  Simplification rules
% 3.41/1.57  ----------------------
% 3.41/1.57  #Subsume      : 75
% 3.41/1.57  #Demod        : 201
% 3.41/1.57  #Tautology    : 178
% 3.41/1.57  #SimpNegUnit  : 21
% 3.41/1.57  #BackRed      : 6
% 3.41/1.57  
% 3.41/1.57  #Partial instantiations: 0
% 3.41/1.57  #Strategies tried      : 1
% 3.41/1.57  
% 3.41/1.57  Timing (in seconds)
% 3.41/1.57  ----------------------
% 3.41/1.57  Preprocessing        : 0.31
% 3.41/1.57  Parsing              : 0.16
% 3.41/1.57  CNF conversion       : 0.02
% 3.41/1.57  Main loop            : 0.47
% 3.41/1.57  Inferencing          : 0.17
% 3.41/1.57  Reduction            : 0.17
% 3.41/1.57  Demodulation         : 0.12
% 3.41/1.57  BG Simplification    : 0.03
% 3.41/1.57  Subsumption          : 0.08
% 3.41/1.57  Abstraction          : 0.03
% 3.41/1.57  MUC search           : 0.00
% 3.41/1.57  Cooper               : 0.00
% 3.41/1.57  Total                : 0.81
% 3.41/1.57  Index Insertion      : 0.00
% 3.41/1.57  Index Deletion       : 0.00
% 3.41/1.57  Index Matching       : 0.00
% 3.41/1.57  BG Taut test         : 0.00
%------------------------------------------------------------------------------

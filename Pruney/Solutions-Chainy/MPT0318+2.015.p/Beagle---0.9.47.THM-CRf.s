%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:04 EST 2020

% Result     : Theorem 1.66s
% Output     : CNFRefutation 1.66s
% Verified   : 
% Statistics : Number of formulae       :   40 (  49 expanded)
%              Number of leaves         :   20 (  26 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  64 expanded)
%              Number of equality atoms :   33 (  56 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_46,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_34,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_26,plain,(
    ! [B_14] : k2_zfmisc_1(k1_xboole_0,B_14) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_6,plain,(
    ! [C_6] : r2_hidden(C_6,k1_tarski(C_6)) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_32,plain,
    ( k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_100,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_110,plain,(
    ! [B_30,A_31] :
      ( k1_xboole_0 = B_30
      | k1_xboole_0 = A_31
      | k2_zfmisc_1(A_31,B_30) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_113,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_100,c_110])).

tff(c_122,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_113])).

tff(c_28,plain,(
    ! [B_16,A_15] :
      ( ~ r2_hidden(B_16,A_15)
      | k4_xboole_0(A_15,k1_tarski(B_16)) != A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_132,plain,(
    ! [A_15] :
      ( ~ r2_hidden('#skF_4',A_15)
      | k4_xboole_0(A_15,k1_xboole_0) != A_15 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_122,c_28])).

tff(c_148,plain,(
    ! [A_32] : ~ r2_hidden('#skF_4',A_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_132])).

tff(c_153,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_6,c_148])).

tff(c_154,plain,(
    k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_160,plain,(
    ! [B_33,A_34] :
      ( k1_xboole_0 = B_33
      | k1_xboole_0 = A_34
      | k2_zfmisc_1(A_34,B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_163,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_154,c_160])).

tff(c_172,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_163])).

tff(c_155,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_177,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_172,c_155])).

tff(c_181,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_177])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n006.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:46:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.66/1.15  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.15  
% 1.66/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.16  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.66/1.16  
% 1.66/1.16  %Foreground sorts:
% 1.66/1.16  
% 1.66/1.16  
% 1.66/1.16  %Background operators:
% 1.66/1.16  
% 1.66/1.16  
% 1.66/1.16  %Foreground operators:
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.66/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.66/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.66/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.66/1.16  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.66/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.66/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.66/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.66/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.66/1.16  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.66/1.16  tff('#skF_4', type, '#skF_4': $i).
% 1.66/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.66/1.16  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.66/1.16  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.66/1.16  
% 1.66/1.17  tff(f_46, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.66/1.17  tff(f_61, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 1.66/1.17  tff(f_34, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 1.66/1.17  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 1.66/1.17  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.66/1.17  tff(c_26, plain, (![B_14]: (k2_zfmisc_1(k1_xboole_0, B_14)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.66/1.17  tff(c_34, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.66/1.17  tff(c_6, plain, (![C_6]: (r2_hidden(C_6, k1_tarski(C_6)))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.66/1.17  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.66/1.17  tff(c_32, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.66/1.17  tff(c_100, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_32])).
% 1.66/1.17  tff(c_110, plain, (![B_30, A_31]: (k1_xboole_0=B_30 | k1_xboole_0=A_31 | k2_zfmisc_1(A_31, B_30)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.66/1.17  tff(c_113, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_100, c_110])).
% 1.66/1.17  tff(c_122, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_34, c_113])).
% 1.66/1.17  tff(c_28, plain, (![B_16, A_15]: (~r2_hidden(B_16, A_15) | k4_xboole_0(A_15, k1_tarski(B_16))!=A_15)), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.66/1.17  tff(c_132, plain, (![A_15]: (~r2_hidden('#skF_4', A_15) | k4_xboole_0(A_15, k1_xboole_0)!=A_15)), inference(superposition, [status(thm), theory('equality')], [c_122, c_28])).
% 1.66/1.17  tff(c_148, plain, (![A_32]: (~r2_hidden('#skF_4', A_32))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_132])).
% 1.66/1.17  tff(c_153, plain, $false, inference(resolution, [status(thm)], [c_6, c_148])).
% 1.66/1.17  tff(c_154, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 1.66/1.17  tff(c_160, plain, (![B_33, A_34]: (k1_xboole_0=B_33 | k1_xboole_0=A_34 | k2_zfmisc_1(A_34, B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.66/1.17  tff(c_163, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_154, c_160])).
% 1.66/1.17  tff(c_172, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_34, c_163])).
% 1.66/1.17  tff(c_155, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_32])).
% 1.66/1.17  tff(c_177, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_172, c_155])).
% 1.66/1.17  tff(c_181, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_177])).
% 1.66/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.66/1.17  
% 1.66/1.17  Inference rules
% 1.66/1.17  ----------------------
% 1.66/1.17  #Ref     : 0
% 1.66/1.17  #Sup     : 33
% 1.66/1.17  #Fact    : 0
% 1.66/1.17  #Define  : 0
% 1.66/1.17  #Split   : 1
% 1.66/1.17  #Chain   : 0
% 1.66/1.17  #Close   : 0
% 1.66/1.17  
% 1.66/1.17  Ordering : KBO
% 1.66/1.17  
% 1.66/1.17  Simplification rules
% 1.66/1.17  ----------------------
% 1.66/1.17  #Subsume      : 0
% 1.66/1.17  #Demod        : 7
% 1.66/1.17  #Tautology    : 28
% 1.66/1.17  #SimpNegUnit  : 2
% 1.66/1.17  #BackRed      : 3
% 1.66/1.17  
% 1.66/1.17  #Partial instantiations: 0
% 1.66/1.17  #Strategies tried      : 1
% 1.66/1.17  
% 1.66/1.17  Timing (in seconds)
% 1.66/1.17  ----------------------
% 1.66/1.17  Preprocessing        : 0.28
% 1.66/1.17  Parsing              : 0.15
% 1.66/1.17  CNF conversion       : 0.02
% 1.66/1.17  Main loop            : 0.12
% 1.66/1.17  Inferencing          : 0.04
% 1.66/1.17  Reduction            : 0.04
% 1.66/1.17  Demodulation         : 0.02
% 1.66/1.17  BG Simplification    : 0.01
% 1.66/1.17  Subsumption          : 0.02
% 1.66/1.17  Abstraction          : 0.01
% 1.66/1.17  MUC search           : 0.00
% 1.66/1.17  Cooper               : 0.00
% 1.66/1.17  Total                : 0.42
% 1.66/1.17  Index Insertion      : 0.00
% 1.66/1.17  Index Deletion       : 0.00
% 1.66/1.17  Index Matching       : 0.00
% 1.66/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------

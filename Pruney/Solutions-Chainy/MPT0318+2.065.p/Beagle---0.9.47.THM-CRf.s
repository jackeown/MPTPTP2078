%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:10 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   40 (  59 expanded)
%              Number of leaves         :   19 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   43 (  88 expanded)
%              Number of equality atoms :   31 (  76 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_39,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_29,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_xboole_0
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_14,plain,(
    ! [B_9] : k2_zfmisc_1(k1_xboole_0,B_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,
    ( k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_94,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k1_xboole_0 = B_9
      | k1_xboole_0 = A_8
      | k2_zfmisc_1(A_8,B_9) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_98,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_10])).

tff(c_103,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_98])).

tff(c_4,plain,(
    ! [A_2] : k2_tarski(A_2,A_2) = k1_tarski(A_2) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_118,plain,(
    ! [B_28,C_29,A_30] :
      ( r2_hidden(B_28,C_29)
      | k4_xboole_0(k2_tarski(A_30,B_28),C_29) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_122,plain,(
    ! [A_31,C_32] :
      ( r2_hidden(A_31,C_32)
      | k4_xboole_0(k1_tarski(A_31),C_32) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_118])).

tff(c_125,plain,(
    ! [C_32] :
      ( r2_hidden('#skF_2',C_32)
      | k4_xboole_0(k1_xboole_0,C_32) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_122])).

tff(c_127,plain,(
    ! [C_32] : r2_hidden('#skF_2',C_32) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_125])).

tff(c_18,plain,(
    ! [C_12,B_11] : ~ r2_hidden(C_12,k4_xboole_0(B_11,k1_tarski(C_12))) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_110,plain,(
    ! [B_11] : ~ r2_hidden('#skF_2',k4_xboole_0(B_11,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_103,c_18])).

tff(c_138,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_110])).

tff(c_139,plain,(
    k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_144,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_139,c_10])).

tff(c_149,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_144])).

tff(c_140,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_161,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_149,c_140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n002.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:37:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.15  
% 1.86/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.15  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.86/1.15  
% 1.86/1.15  %Foreground sorts:
% 1.86/1.15  
% 1.86/1.15  
% 1.86/1.15  %Background operators:
% 1.86/1.15  
% 1.86/1.15  
% 1.86/1.15  %Foreground operators:
% 1.86/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.15  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.86/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.86/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.86/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.86/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.86/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.86/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.15  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.86/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.15  
% 1.86/1.16  tff(f_39, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.86/1.16  tff(f_62, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 1.86/1.16  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 1.86/1.16  tff(f_29, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.86/1.16  tff(f_52, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_xboole_0) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_zfmisc_1)).
% 1.86/1.16  tff(f_46, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 1.86/1.16  tff(c_14, plain, (![B_9]: (k2_zfmisc_1(k1_xboole_0, B_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.86/1.16  tff(c_30, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.86/1.16  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.86/1.16  tff(c_28, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_62])).
% 1.86/1.16  tff(c_94, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_28])).
% 1.86/1.16  tff(c_10, plain, (![B_9, A_8]: (k1_xboole_0=B_9 | k1_xboole_0=A_8 | k2_zfmisc_1(A_8, B_9)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.86/1.16  tff(c_98, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_94, c_10])).
% 1.86/1.16  tff(c_103, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_30, c_98])).
% 1.86/1.16  tff(c_4, plain, (![A_2]: (k2_tarski(A_2, A_2)=k1_tarski(A_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.86/1.16  tff(c_118, plain, (![B_28, C_29, A_30]: (r2_hidden(B_28, C_29) | k4_xboole_0(k2_tarski(A_30, B_28), C_29)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.86/1.16  tff(c_122, plain, (![A_31, C_32]: (r2_hidden(A_31, C_32) | k4_xboole_0(k1_tarski(A_31), C_32)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_4, c_118])).
% 1.86/1.16  tff(c_125, plain, (![C_32]: (r2_hidden('#skF_2', C_32) | k4_xboole_0(k1_xboole_0, C_32)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_103, c_122])).
% 1.86/1.16  tff(c_127, plain, (![C_32]: (r2_hidden('#skF_2', C_32))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_125])).
% 1.86/1.16  tff(c_18, plain, (![C_12, B_11]: (~r2_hidden(C_12, k4_xboole_0(B_11, k1_tarski(C_12))))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.86/1.16  tff(c_110, plain, (![B_11]: (~r2_hidden('#skF_2', k4_xboole_0(B_11, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_103, c_18])).
% 1.86/1.16  tff(c_138, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_127, c_110])).
% 1.86/1.16  tff(c_139, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 1.86/1.16  tff(c_144, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_139, c_10])).
% 1.86/1.16  tff(c_149, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_30, c_144])).
% 1.86/1.16  tff(c_140, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 1.86/1.16  tff(c_161, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_149, c_140])).
% 1.86/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.86/1.16  
% 1.86/1.16  Inference rules
% 1.86/1.16  ----------------------
% 1.86/1.16  #Ref     : 0
% 1.86/1.16  #Sup     : 32
% 1.86/1.16  #Fact    : 0
% 1.86/1.16  #Define  : 0
% 1.86/1.16  #Split   : 1
% 1.86/1.16  #Chain   : 0
% 1.86/1.16  #Close   : 0
% 1.86/1.16  
% 1.86/1.16  Ordering : KBO
% 1.86/1.16  
% 1.86/1.16  Simplification rules
% 1.86/1.16  ----------------------
% 1.86/1.16  #Subsume      : 2
% 1.86/1.16  #Demod        : 8
% 1.86/1.16  #Tautology    : 24
% 1.86/1.16  #SimpNegUnit  : 3
% 1.86/1.16  #BackRed      : 3
% 1.86/1.16  
% 1.86/1.16  #Partial instantiations: 0
% 1.86/1.16  #Strategies tried      : 1
% 1.86/1.16  
% 1.86/1.16  Timing (in seconds)
% 1.86/1.16  ----------------------
% 1.86/1.16  Preprocessing        : 0.29
% 1.86/1.17  Parsing              : 0.15
% 1.86/1.17  CNF conversion       : 0.02
% 1.86/1.17  Main loop            : 0.11
% 1.86/1.17  Inferencing          : 0.03
% 1.86/1.17  Reduction            : 0.04
% 1.86/1.17  Demodulation         : 0.02
% 1.86/1.17  BG Simplification    : 0.01
% 1.86/1.17  Subsumption          : 0.02
% 1.86/1.17  Abstraction          : 0.00
% 1.86/1.17  MUC search           : 0.00
% 1.86/1.17  Cooper               : 0.00
% 1.86/1.17  Total                : 0.43
% 1.86/1.17  Index Insertion      : 0.00
% 1.86/1.17  Index Deletion       : 0.00
% 1.86/1.17  Index Matching       : 0.00
% 1.86/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------

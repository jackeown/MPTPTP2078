%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:08 EST 2020

% Result     : Theorem 1.89s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   37 (  48 expanded)
%              Number of leaves         :   19 (  26 expanded)
%              Depth                    :    4
%              Number of atoms          :   39 (  64 expanded)
%              Number of equality atoms :   37 (  62 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_45,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(A,k2_tarski(B,C)) = k1_xboole_0
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_38,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_10,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_220,plain,(
    ! [B_48,C_49] : k4_xboole_0(k1_tarski(B_48),k2_tarski(B_48,C_49)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_227,plain,(
    ! [A_9] : k4_xboole_0(k1_tarski(A_9),k1_tarski(A_9)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_220])).

tff(c_20,plain,(
    ! [B_15] : k4_xboole_0(k1_tarski(B_15),k1_tarski(B_15)) != k1_tarski(B_15) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_230,plain,(
    ! [B_15] : k1_tarski(B_15) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_227,c_20])).

tff(c_100,plain,(
    ! [B_32,C_33] : k4_xboole_0(k1_tarski(B_32),k2_tarski(B_32,C_33)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_107,plain,(
    ! [A_9] : k4_xboole_0(k1_tarski(A_9),k1_tarski(A_9)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_100])).

tff(c_110,plain,(
    ! [B_15] : k1_tarski(B_15) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_107,c_20])).

tff(c_36,plain,
    ( k2_zfmisc_1('#skF_2',k1_tarski('#skF_3')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_95,plain,(
    k2_zfmisc_1(k1_tarski('#skF_3'),'#skF_2') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_200,plain,(
    ! [B_46,A_47] :
      ( k1_xboole_0 = B_46
      | k1_xboole_0 = A_47
      | k2_zfmisc_1(A_47,B_46) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_203,plain,
    ( k1_xboole_0 = '#skF_2'
    | k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_95,c_200])).

tff(c_213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_38,c_203])).

tff(c_214,plain,(
    k2_zfmisc_1('#skF_2',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_313,plain,(
    ! [B_59,A_60] :
      ( k1_xboole_0 = B_59
      | k1_xboole_0 = A_60
      | k2_zfmisc_1(A_60,B_59) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_316,plain,
    ( k1_tarski('#skF_3') = k1_xboole_0
    | k1_xboole_0 = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_313])).

tff(c_326,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_38,c_230,c_316])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n004.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:38 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.89/1.27  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.27  
% 1.89/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.28  %$ r2_hidden > r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.89/1.28  
% 1.89/1.28  %Foreground sorts:
% 1.89/1.28  
% 1.89/1.28  
% 1.89/1.28  %Background operators:
% 1.89/1.28  
% 1.89/1.28  
% 1.89/1.28  %Foreground operators:
% 1.89/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.89/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.89/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.89/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.89/1.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.89/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.89/1.28  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.89/1.28  tff('#skF_2', type, '#skF_2': $i).
% 1.89/1.28  tff('#skF_3', type, '#skF_3': $i).
% 1.89/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.89/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.89/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.89/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.89/1.28  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.89/1.28  
% 2.05/1.29  tff(f_90, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.05/1.29  tff(f_45, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.05/1.29  tff(f_80, axiom, (![A, B, C]: ((k4_xboole_0(A, k2_tarski(B, C)) = k1_xboole_0) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_zfmisc_1)).
% 2.05/1.29  tff(f_61, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.05/1.29  tff(f_51, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.05/1.29  tff(c_38, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.05/1.29  tff(c_10, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_45])).
% 2.05/1.29  tff(c_220, plain, (![B_48, C_49]: (k4_xboole_0(k1_tarski(B_48), k2_tarski(B_48, C_49))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.05/1.29  tff(c_227, plain, (![A_9]: (k4_xboole_0(k1_tarski(A_9), k1_tarski(A_9))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_220])).
% 2.05/1.29  tff(c_20, plain, (![B_15]: (k4_xboole_0(k1_tarski(B_15), k1_tarski(B_15))!=k1_tarski(B_15))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.05/1.29  tff(c_230, plain, (![B_15]: (k1_tarski(B_15)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_227, c_20])).
% 2.05/1.29  tff(c_100, plain, (![B_32, C_33]: (k4_xboole_0(k1_tarski(B_32), k2_tarski(B_32, C_33))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.05/1.29  tff(c_107, plain, (![A_9]: (k4_xboole_0(k1_tarski(A_9), k1_tarski(A_9))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_100])).
% 2.05/1.29  tff(c_110, plain, (![B_15]: (k1_tarski(B_15)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_107, c_20])).
% 2.05/1.29  tff(c_36, plain, (k2_zfmisc_1('#skF_2', k1_tarski('#skF_3'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_2')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.05/1.29  tff(c_95, plain, (k2_zfmisc_1(k1_tarski('#skF_3'), '#skF_2')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_36])).
% 2.05/1.29  tff(c_200, plain, (![B_46, A_47]: (k1_xboole_0=B_46 | k1_xboole_0=A_47 | k2_zfmisc_1(A_47, B_46)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.29  tff(c_203, plain, (k1_xboole_0='#skF_2' | k1_tarski('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_95, c_200])).
% 2.05/1.29  tff(c_213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_38, c_203])).
% 2.05/1.29  tff(c_214, plain, (k2_zfmisc_1('#skF_2', k1_tarski('#skF_3'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_36])).
% 2.05/1.29  tff(c_313, plain, (![B_59, A_60]: (k1_xboole_0=B_59 | k1_xboole_0=A_60 | k2_zfmisc_1(A_60, B_59)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.29  tff(c_316, plain, (k1_tarski('#skF_3')=k1_xboole_0 | k1_xboole_0='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_214, c_313])).
% 2.05/1.29  tff(c_326, plain, $false, inference(negUnitSimplification, [status(thm)], [c_38, c_230, c_316])).
% 2.05/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.29  
% 2.05/1.29  Inference rules
% 2.05/1.29  ----------------------
% 2.05/1.29  #Ref     : 0
% 2.05/1.29  #Sup     : 79
% 2.05/1.29  #Fact    : 0
% 2.05/1.29  #Define  : 0
% 2.05/1.29  #Split   : 1
% 2.05/1.29  #Chain   : 0
% 2.05/1.29  #Close   : 0
% 2.05/1.29  
% 2.05/1.29  Ordering : KBO
% 2.05/1.29  
% 2.05/1.29  Simplification rules
% 2.05/1.29  ----------------------
% 2.05/1.29  #Subsume      : 0
% 2.05/1.29  #Demod        : 12
% 2.05/1.29  #Tautology    : 52
% 2.05/1.29  #SimpNegUnit  : 2
% 2.05/1.29  #BackRed      : 2
% 2.05/1.29  
% 2.05/1.29  #Partial instantiations: 0
% 2.05/1.29  #Strategies tried      : 1
% 2.05/1.29  
% 2.05/1.29  Timing (in seconds)
% 2.05/1.29  ----------------------
% 2.05/1.29  Preprocessing        : 0.31
% 2.05/1.29  Parsing              : 0.16
% 2.05/1.29  CNF conversion       : 0.02
% 2.05/1.29  Main loop            : 0.17
% 2.05/1.29  Inferencing          : 0.06
% 2.05/1.29  Reduction            : 0.06
% 2.05/1.29  Demodulation         : 0.04
% 2.05/1.29  BG Simplification    : 0.01
% 2.05/1.29  Subsumption          : 0.03
% 2.05/1.29  Abstraction          : 0.01
% 2.05/1.29  MUC search           : 0.00
% 2.05/1.29  Cooper               : 0.00
% 2.05/1.29  Total                : 0.51
% 2.05/1.29  Index Insertion      : 0.00
% 2.05/1.29  Index Deletion       : 0.00
% 2.05/1.29  Index Matching       : 0.00
% 2.05/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------

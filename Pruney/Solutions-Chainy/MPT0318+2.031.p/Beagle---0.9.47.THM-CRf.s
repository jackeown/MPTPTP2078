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
% DateTime   : Thu Dec  3 09:54:06 EST 2020

% Result     : Theorem 1.82s
% Output     : CNFRefutation 1.82s
% Verified   : 
% Statistics : Number of formulae       :   43 (  52 expanded)
%              Number of leaves         :   21 (  27 expanded)
%              Depth                    :    7
%              Number of atoms          :   45 (  68 expanded)
%              Number of equality atoms :   36 (  59 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_48,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_63,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_38,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_36,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_53,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,k1_tarski(B)) = A
    <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(c_32,plain,(
    ! [B_15] : k2_zfmisc_1(k1_xboole_0,B_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_40,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_74,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    ! [D_7,A_2] : r2_hidden(D_7,k2_tarski(A_2,D_7)) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_80,plain,(
    ! [A_25] : r2_hidden(A_25,k1_tarski(A_25)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_6])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,
    ( k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_91,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_106,plain,(
    ! [B_31,A_32] :
      ( k1_xboole_0 = B_31
      | k1_xboole_0 = A_32
      | k2_zfmisc_1(A_32,B_31) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_109,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_106])).

tff(c_118,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_109])).

tff(c_34,plain,(
    ! [B_17,A_16] :
      ( ~ r2_hidden(B_17,A_16)
      | k4_xboole_0(A_16,k1_tarski(B_17)) != A_16 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_128,plain,(
    ! [A_16] :
      ( ~ r2_hidden('#skF_4',A_16)
      | k4_xboole_0(A_16,k1_xboole_0) != A_16 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_118,c_34])).

tff(c_154,plain,(
    ! [A_35] : ~ r2_hidden('#skF_4',A_35) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_128])).

tff(c_165,plain,(
    $false ),
    inference(resolution,[status(thm)],[c_80,c_154])).

tff(c_166,plain,(
    k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_190,plain,(
    ! [B_40,A_41] :
      ( k1_xboole_0 = B_40
      | k1_xboole_0 = A_41
      | k2_zfmisc_1(A_41,B_40) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_193,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_190])).

tff(c_202,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_40,c_193])).

tff(c_167,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_207,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_167])).

tff(c_211,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_207])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 19:49:21 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.82/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.21  
% 1.82/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.22  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.82/1.22  
% 1.82/1.22  %Foreground sorts:
% 1.82/1.22  
% 1.82/1.22  
% 1.82/1.22  %Background operators:
% 1.82/1.22  
% 1.82/1.22  
% 1.82/1.22  %Foreground operators:
% 1.82/1.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.82/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.82/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.82/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.82/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.82/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.82/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.82/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.82/1.22  tff('#skF_3', type, '#skF_3': $i).
% 1.82/1.22  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.82/1.22  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.82/1.22  tff('#skF_4', type, '#skF_4': $i).
% 1.82/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.82/1.22  
% 1.82/1.23  tff(f_48, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.82/1.23  tff(f_63, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 1.82/1.23  tff(f_38, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.82/1.23  tff(f_36, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.82/1.23  tff(f_27, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 1.82/1.23  tff(f_53, axiom, (![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 1.82/1.23  tff(c_32, plain, (![B_15]: (k2_zfmisc_1(k1_xboole_0, B_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.82/1.23  tff(c_40, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.82/1.23  tff(c_74, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.82/1.23  tff(c_6, plain, (![D_7, A_2]: (r2_hidden(D_7, k2_tarski(A_2, D_7)))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.82/1.23  tff(c_80, plain, (![A_25]: (r2_hidden(A_25, k1_tarski(A_25)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_6])).
% 1.82/1.23  tff(c_2, plain, (![A_1]: (k4_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.82/1.23  tff(c_38, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_63])).
% 1.82/1.23  tff(c_91, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_38])).
% 1.82/1.23  tff(c_106, plain, (![B_31, A_32]: (k1_xboole_0=B_31 | k1_xboole_0=A_32 | k2_zfmisc_1(A_32, B_31)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.82/1.23  tff(c_109, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_91, c_106])).
% 1.82/1.23  tff(c_118, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_40, c_109])).
% 1.82/1.23  tff(c_34, plain, (![B_17, A_16]: (~r2_hidden(B_17, A_16) | k4_xboole_0(A_16, k1_tarski(B_17))!=A_16)), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.82/1.23  tff(c_128, plain, (![A_16]: (~r2_hidden('#skF_4', A_16) | k4_xboole_0(A_16, k1_xboole_0)!=A_16)), inference(superposition, [status(thm), theory('equality')], [c_118, c_34])).
% 1.82/1.23  tff(c_154, plain, (![A_35]: (~r2_hidden('#skF_4', A_35))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_128])).
% 1.82/1.23  tff(c_165, plain, $false, inference(resolution, [status(thm)], [c_80, c_154])).
% 1.82/1.23  tff(c_166, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 1.82/1.23  tff(c_190, plain, (![B_40, A_41]: (k1_xboole_0=B_40 | k1_xboole_0=A_41 | k2_zfmisc_1(A_41, B_40)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.82/1.23  tff(c_193, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_166, c_190])).
% 1.82/1.23  tff(c_202, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_40, c_193])).
% 1.82/1.23  tff(c_167, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_38])).
% 1.82/1.23  tff(c_207, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_202, c_167])).
% 1.82/1.23  tff(c_211, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_207])).
% 1.82/1.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.82/1.23  
% 1.82/1.23  Inference rules
% 1.82/1.23  ----------------------
% 1.82/1.23  #Ref     : 0
% 1.82/1.23  #Sup     : 39
% 1.82/1.23  #Fact    : 0
% 1.82/1.23  #Define  : 0
% 1.82/1.23  #Split   : 1
% 1.82/1.23  #Chain   : 0
% 1.82/1.23  #Close   : 0
% 1.82/1.23  
% 1.82/1.23  Ordering : KBO
% 1.82/1.23  
% 1.82/1.23  Simplification rules
% 1.82/1.23  ----------------------
% 1.82/1.23  #Subsume      : 0
% 1.82/1.23  #Demod        : 8
% 1.82/1.23  #Tautology    : 32
% 1.82/1.23  #SimpNegUnit  : 2
% 1.82/1.23  #BackRed      : 3
% 1.82/1.23  
% 1.82/1.23  #Partial instantiations: 0
% 1.82/1.23  #Strategies tried      : 1
% 1.82/1.23  
% 1.82/1.23  Timing (in seconds)
% 1.82/1.23  ----------------------
% 1.82/1.23  Preprocessing        : 0.31
% 1.82/1.23  Parsing              : 0.16
% 1.82/1.23  CNF conversion       : 0.02
% 1.82/1.23  Main loop            : 0.14
% 1.82/1.23  Inferencing          : 0.05
% 1.82/1.23  Reduction            : 0.05
% 1.82/1.23  Demodulation         : 0.04
% 1.82/1.23  BG Simplification    : 0.01
% 1.82/1.23  Subsumption          : 0.03
% 1.82/1.23  Abstraction          : 0.01
% 1.82/1.23  MUC search           : 0.00
% 1.82/1.23  Cooper               : 0.00
% 1.82/1.23  Total                : 0.48
% 1.82/1.23  Index Insertion      : 0.00
% 1.82/1.23  Index Deletion       : 0.00
% 1.82/1.23  Index Matching       : 0.00
% 1.82/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

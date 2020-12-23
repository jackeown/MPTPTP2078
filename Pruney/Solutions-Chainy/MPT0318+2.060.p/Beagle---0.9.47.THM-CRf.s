%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:09 EST 2020

% Result     : Theorem 1.86s
% Output     : CNFRefutation 1.86s
% Verified   : 
% Statistics : Number of formulae       :   33 (  51 expanded)
%              Number of leaves         :   15 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  76 expanded)
%              Number of equality atoms :   32 (  74 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_35,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(c_10,plain,(
    ! [B_4] : k2_zfmisc_1(k1_xboole_0,B_4) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_30,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_28,plain,
    ( k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_78,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_98,plain,(
    ! [B_28,A_29] :
      ( k1_xboole_0 = B_28
      | k1_xboole_0 = A_29
      | k2_zfmisc_1(A_29,B_28) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_101,plain,
    ( k1_xboole_0 = '#skF_1'
    | k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_98])).

tff(c_110,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_101])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [B_6] : k4_xboole_0(k1_tarski(B_6),k1_tarski(B_6)) != k1_tarski(B_6) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_142,plain,(
    k4_xboole_0(k1_xboole_0,k1_tarski('#skF_2')) != k1_tarski('#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_12])).

tff(c_165,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_110,c_2,c_142])).

tff(c_166,plain,(
    k2_zfmisc_1('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_187,plain,(
    ! [B_37,A_38] :
      ( k1_xboole_0 = B_37
      | k1_xboole_0 = A_38
      | k2_zfmisc_1(A_38,B_37) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_190,plain,
    ( k1_tarski('#skF_2') = k1_xboole_0
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_166,c_187])).

tff(c_199,plain,(
    k1_tarski('#skF_2') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_30,c_190])).

tff(c_167,plain,(
    k2_zfmisc_1(k1_tarski('#skF_2'),'#skF_1') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_204,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_1') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_199,c_167])).

tff(c_208,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_204])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.11/0.32  % Computer   : n005.cluster.edu
% 0.11/0.32  % Model      : x86_64 x86_64
% 0.11/0.32  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.11/0.32  % Memory     : 8042.1875MB
% 0.11/0.32  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.11/0.32  % CPULimit   : 60
% 0.11/0.32  % DateTime   : Tue Dec  1 20:34:32 EST 2020
% 0.11/0.33  % CPUTime    : 
% 0.11/0.33  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.86/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.20  
% 1.86/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.20  %$ r1_tarski > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.86/1.20  
% 1.86/1.20  %Foreground sorts:
% 1.86/1.20  
% 1.86/1.20  
% 1.86/1.20  %Background operators:
% 1.86/1.20  
% 1.86/1.20  
% 1.86/1.20  %Foreground operators:
% 1.86/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.86/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.86/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.86/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.86/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.86/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.86/1.20  tff('#skF_2', type, '#skF_2': $i).
% 1.86/1.20  tff('#skF_1', type, '#skF_1': $i).
% 1.86/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.86/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 1.86/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.86/1.20  
% 1.86/1.21  tff(f_35, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 1.86/1.21  tff(f_69, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 1.86/1.21  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_boole)).
% 1.86/1.21  tff(f_40, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.86/1.21  tff(c_10, plain, (![B_4]: (k2_zfmisc_1(k1_xboole_0, B_4)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.86/1.21  tff(c_30, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.86/1.21  tff(c_28, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 1.86/1.21  tff(c_78, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_28])).
% 1.86/1.21  tff(c_98, plain, (![B_28, A_29]: (k1_xboole_0=B_28 | k1_xboole_0=A_29 | k2_zfmisc_1(A_29, B_28)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.86/1.21  tff(c_101, plain, (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_78, c_98])).
% 1.86/1.21  tff(c_110, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_30, c_101])).
% 1.86/1.21  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.86/1.21  tff(c_12, plain, (![B_6]: (k4_xboole_0(k1_tarski(B_6), k1_tarski(B_6))!=k1_tarski(B_6))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.86/1.21  tff(c_142, plain, (k4_xboole_0(k1_xboole_0, k1_tarski('#skF_2'))!=k1_tarski('#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_110, c_12])).
% 1.86/1.21  tff(c_165, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_110, c_2, c_142])).
% 1.86/1.21  tff(c_166, plain, (k2_zfmisc_1('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 1.86/1.21  tff(c_187, plain, (![B_37, A_38]: (k1_xboole_0=B_37 | k1_xboole_0=A_38 | k2_zfmisc_1(A_38, B_37)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.86/1.21  tff(c_190, plain, (k1_tarski('#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_166, c_187])).
% 1.86/1.21  tff(c_199, plain, (k1_tarski('#skF_2')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_30, c_190])).
% 1.86/1.21  tff(c_167, plain, (k2_zfmisc_1(k1_tarski('#skF_2'), '#skF_1')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_28])).
% 1.86/1.21  tff(c_204, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_1')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_199, c_167])).
% 1.86/1.21  tff(c_208, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_204])).
% 1.86/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.86/1.21  
% 1.86/1.21  Inference rules
% 1.86/1.21  ----------------------
% 1.86/1.21  #Ref     : 0
% 1.86/1.21  #Sup     : 42
% 1.86/1.21  #Fact    : 0
% 1.86/1.21  #Define  : 0
% 1.86/1.21  #Split   : 1
% 1.86/1.21  #Chain   : 0
% 1.86/1.21  #Close   : 0
% 1.86/1.21  
% 1.86/1.21  Ordering : KBO
% 1.86/1.21  
% 1.86/1.21  Simplification rules
% 1.86/1.21  ----------------------
% 1.86/1.21  #Subsume      : 0
% 1.86/1.21  #Demod        : 18
% 1.86/1.21  #Tautology    : 30
% 1.86/1.21  #SimpNegUnit  : 2
% 1.86/1.21  #BackRed      : 3
% 1.86/1.21  
% 1.86/1.21  #Partial instantiations: 0
% 1.86/1.21  #Strategies tried      : 1
% 1.86/1.21  
% 1.86/1.21  Timing (in seconds)
% 1.86/1.21  ----------------------
% 1.86/1.21  Preprocessing        : 0.29
% 1.86/1.21  Parsing              : 0.15
% 1.86/1.21  CNF conversion       : 0.02
% 1.86/1.21  Main loop            : 0.13
% 1.86/1.21  Inferencing          : 0.05
% 1.86/1.21  Reduction            : 0.05
% 1.86/1.21  Demodulation         : 0.03
% 1.86/1.21  BG Simplification    : 0.01
% 1.86/1.21  Subsumption          : 0.03
% 1.86/1.21  Abstraction          : 0.01
% 1.86/1.21  MUC search           : 0.00
% 1.86/1.21  Cooper               : 0.00
% 1.86/1.21  Total                : 0.45
% 1.86/1.21  Index Insertion      : 0.00
% 1.86/1.21  Index Deletion       : 0.00
% 1.86/1.21  Index Matching       : 0.00
% 1.86/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

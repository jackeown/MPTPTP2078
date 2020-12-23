%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:03 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   47 (  56 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   48 (  71 expanded)
%              Number of equality atoms :   37 (  60 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_56,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(f_73,negated_conjecture,(
    ~ ! [A,B] :
        ( A != k1_xboole_0
       => ( k2_zfmisc_1(k1_tarski(B),A) != k1_xboole_0
          & k2_zfmisc_1(A,k1_tarski(B)) != k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t130_zfmisc_1)).

tff(f_27,axiom,(
    ! [A] : k4_xboole_0(k1_xboole_0,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_boole)).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_40,plain,(
    ! [B_20] : k2_zfmisc_1(k1_xboole_0,B_20) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_50,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_2,plain,(
    ! [A_1] : k4_xboole_0(k1_xboole_0,A_1) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_89,plain,(
    ! [C_28,B_29] : ~ r2_hidden(C_28,k4_xboole_0(B_29,k1_tarski(C_28))) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_92,plain,(
    ! [C_28] : ~ r2_hidden(C_28,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_89])).

tff(c_48,plain,
    ( k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0
    | k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_96,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_125,plain,(
    ! [B_45,A_46] :
      ( k1_xboole_0 = B_45
      | k1_xboole_0 = A_46
      | k2_zfmisc_1(A_46,B_45) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_128,plain,
    ( k1_xboole_0 = '#skF_3'
    | k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_125])).

tff(c_137,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_128])).

tff(c_28,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_102,plain,(
    ! [A_40,B_41] : k1_enumset1(A_40,A_40,B_41) = k2_tarski(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_8,plain,(
    ! [E_8,A_2,C_4] : r2_hidden(E_8,k1_enumset1(A_2,E_8,C_4)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_120,plain,(
    ! [A_42,B_43] : r2_hidden(A_42,k2_tarski(A_42,B_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_8])).

tff(c_123,plain,(
    ! [A_9] : r2_hidden(A_9,k1_tarski(A_9)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_120])).

tff(c_147,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_137,c_123])).

tff(c_154,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_92,c_147])).

tff(c_155,plain,(
    k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_191,plain,(
    ! [B_57,A_58] :
      ( k1_xboole_0 = B_57
      | k1_xboole_0 = A_58
      | k2_zfmisc_1(A_58,B_57) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_194,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_191])).

tff(c_203,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_194])).

tff(c_156,plain,(
    k2_zfmisc_1(k1_tarski('#skF_4'),'#skF_3') != k1_xboole_0 ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_208,plain,(
    k2_zfmisc_1(k1_xboole_0,'#skF_3') != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_156])).

tff(c_212,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_208])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:09:51 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.20  
% 2.04/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.20  %$ r2_hidden > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 2.04/1.20  
% 2.04/1.20  %Foreground sorts:
% 2.04/1.20  
% 2.04/1.20  
% 2.04/1.20  %Background operators:
% 2.04/1.20  
% 2.04/1.20  
% 2.04/1.20  %Foreground operators:
% 2.04/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.04/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.04/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.20  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.04/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.04/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.04/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.04/1.20  tff('#skF_3', type, '#skF_3': $i).
% 2.04/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.20  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.04/1.20  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 2.04/1.20  
% 2.04/1.21  tff(f_56, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 2.04/1.21  tff(f_73, negated_conjecture, ~(![A, B]: (~(A = k1_xboole_0) => (~(k2_zfmisc_1(k1_tarski(B), A) = k1_xboole_0) & ~(k2_zfmisc_1(A, k1_tarski(B)) = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t130_zfmisc_1)).
% 2.04/1.21  tff(f_27, axiom, (![A]: (k4_xboole_0(k1_xboole_0, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_boole)).
% 2.04/1.21  tff(f_63, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.04/1.21  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.04/1.21  tff(f_46, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 2.04/1.21  tff(f_42, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 2.04/1.21  tff(c_40, plain, (![B_20]: (k2_zfmisc_1(k1_xboole_0, B_20)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.04/1.21  tff(c_50, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.04/1.21  tff(c_2, plain, (![A_1]: (k4_xboole_0(k1_xboole_0, A_1)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.04/1.21  tff(c_89, plain, (![C_28, B_29]: (~r2_hidden(C_28, k4_xboole_0(B_29, k1_tarski(C_28))))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.04/1.21  tff(c_92, plain, (![C_28]: (~r2_hidden(C_28, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_2, c_89])).
% 2.04/1.21  tff(c_48, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0 | k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_73])).
% 2.04/1.21  tff(c_96, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_48])).
% 2.04/1.21  tff(c_125, plain, (![B_45, A_46]: (k1_xboole_0=B_45 | k1_xboole_0=A_46 | k2_zfmisc_1(A_46, B_45)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.04/1.21  tff(c_128, plain, (k1_xboole_0='#skF_3' | k1_tarski('#skF_4')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_96, c_125])).
% 2.04/1.21  tff(c_137, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_50, c_128])).
% 2.04/1.21  tff(c_28, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.04/1.21  tff(c_102, plain, (![A_40, B_41]: (k1_enumset1(A_40, A_40, B_41)=k2_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.04/1.21  tff(c_8, plain, (![E_8, A_2, C_4]: (r2_hidden(E_8, k1_enumset1(A_2, E_8, C_4)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.04/1.21  tff(c_120, plain, (![A_42, B_43]: (r2_hidden(A_42, k2_tarski(A_42, B_43)))), inference(superposition, [status(thm), theory('equality')], [c_102, c_8])).
% 2.04/1.21  tff(c_123, plain, (![A_9]: (r2_hidden(A_9, k1_tarski(A_9)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_120])).
% 2.04/1.21  tff(c_147, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_137, c_123])).
% 2.04/1.21  tff(c_154, plain, $false, inference(negUnitSimplification, [status(thm)], [c_92, c_147])).
% 2.04/1.21  tff(c_155, plain, (k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 2.04/1.21  tff(c_191, plain, (![B_57, A_58]: (k1_xboole_0=B_57 | k1_xboole_0=A_58 | k2_zfmisc_1(A_58, B_57)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.04/1.21  tff(c_194, plain, (k1_tarski('#skF_4')=k1_xboole_0 | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_155, c_191])).
% 2.04/1.21  tff(c_203, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_50, c_194])).
% 2.04/1.21  tff(c_156, plain, (k2_zfmisc_1(k1_tarski('#skF_4'), '#skF_3')!=k1_xboole_0), inference(splitRight, [status(thm)], [c_48])).
% 2.04/1.21  tff(c_208, plain, (k2_zfmisc_1(k1_xboole_0, '#skF_3')!=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_203, c_156])).
% 2.04/1.21  tff(c_212, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_208])).
% 2.04/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.04/1.21  
% 2.04/1.21  Inference rules
% 2.04/1.21  ----------------------
% 2.04/1.21  #Ref     : 0
% 2.04/1.21  #Sup     : 38
% 2.04/1.21  #Fact    : 0
% 2.04/1.21  #Define  : 0
% 2.04/1.21  #Split   : 1
% 2.04/1.21  #Chain   : 0
% 2.04/1.21  #Close   : 0
% 2.04/1.21  
% 2.04/1.21  Ordering : KBO
% 2.04/1.21  
% 2.04/1.21  Simplification rules
% 2.04/1.21  ----------------------
% 2.04/1.21  #Subsume      : 0
% 2.04/1.21  #Demod        : 7
% 2.04/1.21  #Tautology    : 26
% 2.04/1.21  #SimpNegUnit  : 3
% 2.04/1.21  #BackRed      : 3
% 2.04/1.21  
% 2.04/1.21  #Partial instantiations: 0
% 2.04/1.21  #Strategies tried      : 1
% 2.04/1.21  
% 2.04/1.21  Timing (in seconds)
% 2.04/1.21  ----------------------
% 2.04/1.21  Preprocessing        : 0.30
% 2.04/1.21  Parsing              : 0.16
% 2.04/1.21  CNF conversion       : 0.02
% 2.04/1.21  Main loop            : 0.15
% 2.04/1.21  Inferencing          : 0.04
% 2.04/1.21  Reduction            : 0.05
% 2.04/1.22  Demodulation         : 0.03
% 2.04/1.22  BG Simplification    : 0.01
% 2.04/1.22  Subsumption          : 0.03
% 2.04/1.22  Abstraction          : 0.01
% 2.04/1.22  MUC search           : 0.00
% 2.04/1.22  Cooper               : 0.00
% 2.04/1.22  Total                : 0.48
% 2.04/1.22  Index Insertion      : 0.00
% 2.04/1.22  Index Deletion       : 0.00
% 2.04/1.22  Index Matching       : 0.00
% 2.04/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------

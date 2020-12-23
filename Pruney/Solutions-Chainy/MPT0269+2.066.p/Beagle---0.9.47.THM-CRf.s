%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:52 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   31 (  33 expanded)
%              Number of leaves         :   17 (  19 expanded)
%              Depth                    :    7
%              Number of atoms          :   30 (  36 expanded)
%              Number of equality atoms :   16 (  22 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_51,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_27,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_16,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_8,plain,(
    ! [A_7] : k2_tarski(A_7,A_7) = k1_tarski(A_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(k1_tarski(A_5),k1_tarski(B_6)) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [A_1] : r1_tarski(k1_xboole_0,A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_58,plain,(
    ! [A_17,B_18,C_19] :
      ( r1_tarski(A_17,k2_xboole_0(B_18,C_19))
      | ~ r1_tarski(k4_xboole_0(A_17,B_18),C_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_61,plain,(
    ! [C_19] :
      ( r1_tarski('#skF_1',k2_xboole_0(k1_tarski('#skF_2'),C_19))
      | ~ r1_tarski(k1_xboole_0,C_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_58])).

tff(c_64,plain,(
    ! [C_20] : r1_tarski('#skF_1',k2_xboole_0(k1_tarski('#skF_2'),C_20)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_61])).

tff(c_69,plain,(
    ! [B_21] : r1_tarski('#skF_1',k2_tarski('#skF_2',B_21)) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_64])).

tff(c_73,plain,(
    r1_tarski('#skF_1',k1_tarski('#skF_2')) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_69])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( k1_tarski(B_9) = A_8
      | k1_xboole_0 = A_8
      | ~ r1_tarski(A_8,k1_tarski(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_76,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(resolution,[status(thm)],[c_73,c_10])).

tff(c_80,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_16,c_76])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.09/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.09/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 18:30:17 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.09  
% 1.63/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.09  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.63/1.09  
% 1.63/1.09  %Foreground sorts:
% 1.63/1.09  
% 1.63/1.09  
% 1.63/1.09  %Background operators:
% 1.63/1.09  
% 1.63/1.09  
% 1.63/1.09  %Foreground operators:
% 1.63/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.63/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.63/1.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.63/1.09  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.63/1.09  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.63/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.63/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.63/1.09  
% 1.63/1.10  tff(f_51, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 1.63/1.10  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.63/1.10  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.63/1.10  tff(f_27, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 1.63/1.10  tff(f_31, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_xboole_1)).
% 1.63/1.10  tff(f_41, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 1.63/1.10  tff(c_18, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.63/1.10  tff(c_16, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.63/1.10  tff(c_8, plain, (![A_7]: (k2_tarski(A_7, A_7)=k1_tarski(A_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.63/1.10  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(k1_tarski(A_5), k1_tarski(B_6))=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.63/1.10  tff(c_2, plain, (![A_1]: (r1_tarski(k1_xboole_0, A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.63/1.10  tff(c_20, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.63/1.10  tff(c_58, plain, (![A_17, B_18, C_19]: (r1_tarski(A_17, k2_xboole_0(B_18, C_19)) | ~r1_tarski(k4_xboole_0(A_17, B_18), C_19))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.10  tff(c_61, plain, (![C_19]: (r1_tarski('#skF_1', k2_xboole_0(k1_tarski('#skF_2'), C_19)) | ~r1_tarski(k1_xboole_0, C_19))), inference(superposition, [status(thm), theory('equality')], [c_20, c_58])).
% 1.63/1.10  tff(c_64, plain, (![C_20]: (r1_tarski('#skF_1', k2_xboole_0(k1_tarski('#skF_2'), C_20)))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_61])).
% 1.63/1.10  tff(c_69, plain, (![B_21]: (r1_tarski('#skF_1', k2_tarski('#skF_2', B_21)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_64])).
% 1.63/1.10  tff(c_73, plain, (r1_tarski('#skF_1', k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_8, c_69])).
% 1.63/1.10  tff(c_10, plain, (![B_9, A_8]: (k1_tarski(B_9)=A_8 | k1_xboole_0=A_8 | ~r1_tarski(A_8, k1_tarski(B_9)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.63/1.10  tff(c_76, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(resolution, [status(thm)], [c_73, c_10])).
% 1.63/1.10  tff(c_80, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_16, c_76])).
% 1.63/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.63/1.10  
% 1.63/1.10  Inference rules
% 1.63/1.10  ----------------------
% 1.63/1.10  #Ref     : 0
% 1.63/1.10  #Sup     : 12
% 1.63/1.10  #Fact    : 0
% 1.63/1.10  #Define  : 0
% 1.63/1.10  #Split   : 0
% 1.63/1.10  #Chain   : 0
% 1.63/1.10  #Close   : 0
% 1.63/1.10  
% 1.63/1.10  Ordering : KBO
% 1.63/1.10  
% 1.63/1.10  Simplification rules
% 1.63/1.10  ----------------------
% 1.63/1.10  #Subsume      : 0
% 1.63/1.10  #Demod        : 2
% 1.63/1.10  #Tautology    : 9
% 1.63/1.10  #SimpNegUnit  : 1
% 1.63/1.10  #BackRed      : 0
% 1.63/1.10  
% 1.63/1.10  #Partial instantiations: 0
% 1.63/1.10  #Strategies tried      : 1
% 1.63/1.10  
% 1.63/1.10  Timing (in seconds)
% 1.63/1.10  ----------------------
% 1.63/1.11  Preprocessing        : 0.27
% 1.63/1.11  Parsing              : 0.14
% 1.63/1.11  CNF conversion       : 0.02
% 1.63/1.11  Main loop            : 0.08
% 1.63/1.11  Inferencing          : 0.03
% 1.63/1.11  Reduction            : 0.03
% 1.63/1.11  Demodulation         : 0.02
% 1.63/1.11  BG Simplification    : 0.01
% 1.63/1.11  Subsumption          : 0.01
% 1.63/1.11  Abstraction          : 0.00
% 1.63/1.11  MUC search           : 0.00
% 1.63/1.11  Cooper               : 0.00
% 1.63/1.11  Total                : 0.38
% 1.63/1.11  Index Insertion      : 0.00
% 1.63/1.11  Index Deletion       : 0.00
% 1.63/1.11  Index Matching       : 0.00
% 1.63/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------

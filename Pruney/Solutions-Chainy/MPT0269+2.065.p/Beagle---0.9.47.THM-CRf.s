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
% DateTime   : Thu Dec  3 09:52:52 EST 2020

% Result     : Theorem 1.63s
% Output     : CNFRefutation 1.63s
% Verified   : 
% Statistics : Number of formulae       :   31 (  35 expanded)
%              Number of leaves         :   16 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  40 expanded)
%              Number of equality atoms :   31 (  39 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_27,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_46,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(c_12,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_4] : k2_tarski(A_4,A_4) = k1_tarski(A_4) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,k1_xboole_0) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_39,plain,(
    ! [A_13,B_14,C_15] : k2_xboole_0(k2_tarski(A_13,B_14),C_15) != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_46,plain,(
    ! [A_16,B_17] : k2_tarski(A_16,B_17) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_39])).

tff(c_48,plain,(
    ! [A_4] : k1_tarski(A_4) != k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_46])).

tff(c_14,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_16,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_55,plain,(
    ! [A_21,B_22] : k2_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) = k2_xboole_0(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_55])).

tff(c_75,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),'#skF_1') = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_72])).

tff(c_82,plain,(
    ! [C_23,B_24,A_25] :
      ( k1_xboole_0 = C_23
      | k1_xboole_0 = B_24
      | C_23 = B_24
      | k2_xboole_0(B_24,C_23) != k1_tarski(A_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_85,plain,(
    ! [A_25] :
      ( k1_xboole_0 = '#skF_1'
      | k1_tarski('#skF_2') = k1_xboole_0
      | k1_tarski('#skF_2') = '#skF_1'
      | k1_tarski(A_25) != k1_tarski('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_82])).

tff(c_92,plain,(
    ! [A_25] : k1_tarski(A_25) != k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_48,c_14,c_85])).

tff(c_97,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_92])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:03:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.63/1.08  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.09  
% 1.63/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.09  %$ k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
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
% 1.63/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.63/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.63/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.63/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.63/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.63/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.63/1.09  
% 1.63/1.10  tff(f_56, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 1.63/1.10  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.63/1.10  tff(f_27, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.63/1.10  tff(f_46, axiom, (![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 1.63/1.10  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.63/1.10  tff(f_43, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 1.63/1.10  tff(c_12, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.63/1.10  tff(c_6, plain, (![A_4]: (k2_tarski(A_4, A_4)=k1_tarski(A_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.63/1.10  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, k1_xboole_0)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.63/1.10  tff(c_39, plain, (![A_13, B_14, C_15]: (k2_xboole_0(k2_tarski(A_13, B_14), C_15)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.63/1.10  tff(c_46, plain, (![A_16, B_17]: (k2_tarski(A_16, B_17)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2, c_39])).
% 1.63/1.10  tff(c_48, plain, (![A_4]: (k1_tarski(A_4)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6, c_46])).
% 1.63/1.10  tff(c_14, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.63/1.10  tff(c_16, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.63/1.10  tff(c_55, plain, (![A_21, B_22]: (k2_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.63/1.10  tff(c_72, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)=k2_xboole_0(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_16, c_55])).
% 1.63/1.10  tff(c_75, plain, (k2_xboole_0(k1_tarski('#skF_2'), '#skF_1')=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_72])).
% 1.63/1.10  tff(c_82, plain, (![C_23, B_24, A_25]: (k1_xboole_0=C_23 | k1_xboole_0=B_24 | C_23=B_24 | k2_xboole_0(B_24, C_23)!=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.63/1.10  tff(c_85, plain, (![A_25]: (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')=k1_xboole_0 | k1_tarski('#skF_2')='#skF_1' | k1_tarski(A_25)!=k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_75, c_82])).
% 1.63/1.10  tff(c_92, plain, (![A_25]: (k1_tarski(A_25)!=k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_12, c_48, c_14, c_85])).
% 1.63/1.10  tff(c_97, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_92])).
% 1.63/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.63/1.10  
% 1.63/1.10  Inference rules
% 1.63/1.10  ----------------------
% 1.63/1.10  #Ref     : 1
% 1.63/1.10  #Sup     : 21
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
% 1.63/1.10  #Subsume      : 4
% 1.63/1.10  #Demod        : 1
% 1.63/1.10  #Tautology    : 11
% 1.63/1.10  #SimpNegUnit  : 1
% 1.63/1.10  #BackRed      : 0
% 1.63/1.10  
% 1.63/1.10  #Partial instantiations: 0
% 1.63/1.10  #Strategies tried      : 1
% 1.63/1.10  
% 1.63/1.10  Timing (in seconds)
% 1.63/1.10  ----------------------
% 1.63/1.10  Preprocessing        : 0.26
% 1.63/1.10  Parsing              : 0.14
% 1.63/1.10  CNF conversion       : 0.01
% 1.63/1.10  Main loop            : 0.09
% 1.63/1.10  Inferencing          : 0.03
% 1.63/1.10  Reduction            : 0.03
% 1.63/1.10  Demodulation         : 0.02
% 1.63/1.10  BG Simplification    : 0.01
% 1.63/1.10  Subsumption          : 0.01
% 1.63/1.10  Abstraction          : 0.00
% 1.63/1.10  MUC search           : 0.00
% 1.63/1.10  Cooper               : 0.00
% 1.63/1.10  Total                : 0.38
% 1.63/1.10  Index Insertion      : 0.00
% 1.63/1.10  Index Deletion       : 0.00
% 1.63/1.10  Index Matching       : 0.00
% 1.63/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:44 EST 2020

% Result     : Theorem 1.97s
% Output     : CNFRefutation 1.97s
% Verified   : 
% Statistics : Number of formulae       :   39 (  41 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  43 expanded)
%              Number of equality atoms :   36 (  42 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_boole)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(c_24,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_26,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_10,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_147,plain,(
    ! [A_28,B_29] : k4_xboole_0(k1_tarski(A_28),k2_tarski(A_28,B_29)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_154,plain,(
    ! [A_8] : k4_xboole_0(k1_tarski(A_8),k1_tarski(A_8)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_147])).

tff(c_16,plain,(
    ! [B_15] : k4_xboole_0(k1_tarski(B_15),k1_tarski(B_15)) != k1_tarski(B_15) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_164,plain,(
    ! [B_15] : k1_tarski(B_15) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_154,c_16])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_166,plain,(
    ! [A_32,B_33] : k2_xboole_0(A_32,k4_xboole_0(B_33,A_32)) = k2_xboole_0(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_189,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) = k2_xboole_0(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_166])).

tff(c_196,plain,(
    k2_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6,c_189])).

tff(c_306,plain,(
    ! [C_47,B_48,A_49] :
      ( k1_xboole_0 = C_47
      | k1_xboole_0 = B_48
      | C_47 = B_48
      | k2_xboole_0(B_48,C_47) != k1_tarski(A_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_318,plain,(
    ! [A_49] :
      ( k1_tarski('#skF_2') = k1_xboole_0
      | k1_xboole_0 = '#skF_1'
      | k1_tarski('#skF_2') = '#skF_1'
      | k1_tarski(A_49) != k1_tarski('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_306])).

tff(c_338,plain,(
    ! [A_49] : k1_tarski(A_49) != k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_26,c_164,c_318])).

tff(c_344,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_338])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 09:25:27 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.97/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.29  
% 1.97/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.29  %$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.97/1.29  
% 1.97/1.29  %Foreground sorts:
% 1.97/1.29  
% 1.97/1.29  
% 1.97/1.29  %Background operators:
% 1.97/1.29  
% 1.97/1.29  
% 1.97/1.29  %Foreground operators:
% 1.97/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.97/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.97/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.97/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.97/1.29  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.97/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.97/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.97/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.97/1.29  tff('#skF_2', type, '#skF_2': $i).
% 1.97/1.29  tff('#skF_1', type, '#skF_1': $i).
% 1.97/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.97/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.97/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.97/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.97/1.29  
% 1.97/1.30  tff(f_68, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 1.97/1.30  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.97/1.30  tff(f_46, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 1.97/1.30  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.97/1.30  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.97/1.30  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_boole)).
% 1.97/1.30  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 1.97/1.30  tff(f_58, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 1.97/1.30  tff(c_24, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.97/1.30  tff(c_26, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.97/1.30  tff(c_10, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.97/1.30  tff(c_147, plain, (![A_28, B_29]: (k4_xboole_0(k1_tarski(A_28), k2_tarski(A_28, B_29))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.97/1.30  tff(c_154, plain, (![A_8]: (k4_xboole_0(k1_tarski(A_8), k1_tarski(A_8))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_147])).
% 1.97/1.30  tff(c_16, plain, (![B_15]: (k4_xboole_0(k1_tarski(B_15), k1_tarski(B_15))!=k1_tarski(B_15))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.97/1.30  tff(c_164, plain, (![B_15]: (k1_tarski(B_15)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_154, c_16])).
% 1.97/1.30  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.97/1.30  tff(c_6, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.97/1.30  tff(c_28, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_68])).
% 1.97/1.30  tff(c_166, plain, (![A_32, B_33]: (k2_xboole_0(A_32, k4_xboole_0(B_33, A_32))=k2_xboole_0(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.97/1.30  tff(c_189, plain, (k2_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)=k2_xboole_0(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_28, c_166])).
% 1.97/1.30  tff(c_196, plain, (k2_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6, c_189])).
% 1.97/1.30  tff(c_306, plain, (![C_47, B_48, A_49]: (k1_xboole_0=C_47 | k1_xboole_0=B_48 | C_47=B_48 | k2_xboole_0(B_48, C_47)!=k1_tarski(A_49))), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.97/1.30  tff(c_318, plain, (![A_49]: (k1_tarski('#skF_2')=k1_xboole_0 | k1_xboole_0='#skF_1' | k1_tarski('#skF_2')='#skF_1' | k1_tarski(A_49)!=k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_196, c_306])).
% 1.97/1.30  tff(c_338, plain, (![A_49]: (k1_tarski(A_49)!=k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_24, c_26, c_164, c_318])).
% 1.97/1.30  tff(c_344, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_338])).
% 1.97/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.97/1.30  
% 1.97/1.30  Inference rules
% 1.97/1.30  ----------------------
% 1.97/1.30  #Ref     : 1
% 1.97/1.30  #Sup     : 75
% 1.97/1.30  #Fact    : 0
% 1.97/1.30  #Define  : 0
% 1.97/1.30  #Split   : 0
% 1.97/1.30  #Chain   : 0
% 1.97/1.30  #Close   : 0
% 1.97/1.30  
% 1.97/1.30  Ordering : KBO
% 1.97/1.30  
% 1.97/1.30  Simplification rules
% 1.97/1.30  ----------------------
% 1.97/1.30  #Subsume      : 0
% 1.97/1.30  #Demod        : 22
% 1.97/1.30  #Tautology    : 60
% 1.97/1.30  #SimpNegUnit  : 6
% 1.97/1.30  #BackRed      : 0
% 1.97/1.30  
% 1.97/1.30  #Partial instantiations: 0
% 1.97/1.30  #Strategies tried      : 1
% 1.97/1.30  
% 1.97/1.30  Timing (in seconds)
% 1.97/1.30  ----------------------
% 1.97/1.31  Preprocessing        : 0.31
% 1.97/1.31  Parsing              : 0.17
% 1.97/1.31  CNF conversion       : 0.02
% 1.97/1.31  Main loop            : 0.19
% 1.97/1.31  Inferencing          : 0.07
% 1.97/1.31  Reduction            : 0.07
% 1.97/1.31  Demodulation         : 0.05
% 1.97/1.31  BG Simplification    : 0.01
% 1.97/1.31  Subsumption          : 0.03
% 1.97/1.31  Abstraction          : 0.01
% 1.97/1.31  MUC search           : 0.00
% 1.97/1.31  Cooper               : 0.00
% 1.97/1.31  Total                : 0.53
% 1.97/1.31  Index Insertion      : 0.00
% 1.97/1.31  Index Deletion       : 0.00
% 1.97/1.31  Index Matching       : 0.00
% 1.97/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------

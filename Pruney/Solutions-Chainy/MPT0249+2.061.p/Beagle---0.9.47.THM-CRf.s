%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:31 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.78s
% Verified   : 
% Statistics : Number of formulae       :   38 (  67 expanded)
%              Number of leaves         :   17 (  31 expanded)
%              Depth                    :    9
%              Number of atoms          :   46 ( 111 expanded)
%              Number of equality atoms :   28 (  81 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_31,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_18,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_4,plain,(
    ! [A_4] : k2_xboole_0(A_4,k1_xboole_0) = A_4 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_45,plain,(
    ! [A_16,B_17] : r1_tarski(A_16,k2_xboole_0(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_48,plain,(
    ! [A_4] : r1_tarski(A_4,A_4) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_45])).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_54,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_6])).

tff(c_86,plain,(
    ! [B_27,A_28] :
      ( k1_tarski(B_27) = A_28
      | k1_xboole_0 = A_28
      | ~ r1_tarski(A_28,k1_tarski(B_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_93,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_54,c_86])).

tff(c_102,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_93])).

tff(c_106,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_24])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,k2_xboole_0(C_3,B_2))
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_119,plain,(
    ! [A_1] :
      ( r1_tarski(A_1,'#skF_2')
      | ~ r1_tarski(A_1,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_106,c_2])).

tff(c_12,plain,(
    ! [B_11,A_10] :
      ( k1_tarski(B_11) = A_10
      | k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,k1_tarski(B_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_111,plain,(
    ! [A_10] :
      ( k1_tarski('#skF_1') = A_10
      | k1_xboole_0 = A_10
      | ~ r1_tarski(A_10,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_12])).

tff(c_129,plain,(
    ! [A_30] :
      ( A_30 = '#skF_2'
      | k1_xboole_0 = A_30
      | ~ r1_tarski(A_30,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_102,c_111])).

tff(c_150,plain,(
    ! [A_31] :
      ( A_31 = '#skF_2'
      | k1_xboole_0 = A_31
      | ~ r1_tarski(A_31,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_119,c_129])).

tff(c_158,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_48,c_150])).

tff(c_166,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_18,c_22,c_158])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:55:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.17  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.17  
% 1.55/1.17  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.18  %$ r1_tarski > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.55/1.18  
% 1.55/1.18  %Foreground sorts:
% 1.55/1.18  
% 1.55/1.18  
% 1.55/1.18  %Background operators:
% 1.55/1.18  
% 1.55/1.18  
% 1.55/1.18  %Foreground operators:
% 1.55/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.55/1.18  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.55/1.18  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.55/1.18  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.55/1.18  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.55/1.18  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.55/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.55/1.18  tff('#skF_3', type, '#skF_3': $i).
% 1.55/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.55/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.55/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.55/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.55/1.18  
% 1.78/1.19  tff(f_56, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 1.78/1.19  tff(f_31, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 1.78/1.19  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.78/1.19  tff(f_43, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.78/1.19  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.78/1.19  tff(c_18, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.78/1.19  tff(c_22, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.78/1.19  tff(c_4, plain, (![A_4]: (k2_xboole_0(A_4, k1_xboole_0)=A_4)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.78/1.19  tff(c_45, plain, (![A_16, B_17]: (r1_tarski(A_16, k2_xboole_0(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.78/1.19  tff(c_48, plain, (![A_4]: (r1_tarski(A_4, A_4))), inference(superposition, [status(thm), theory('equality')], [c_4, c_45])).
% 1.78/1.19  tff(c_20, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.78/1.19  tff(c_24, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.78/1.19  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.78/1.19  tff(c_54, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_24, c_6])).
% 1.78/1.19  tff(c_86, plain, (![B_27, A_28]: (k1_tarski(B_27)=A_28 | k1_xboole_0=A_28 | ~r1_tarski(A_28, k1_tarski(B_27)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.78/1.19  tff(c_93, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_54, c_86])).
% 1.78/1.19  tff(c_102, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_20, c_93])).
% 1.78/1.19  tff(c_106, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_102, c_24])).
% 1.78/1.19  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, k2_xboole_0(C_3, B_2)) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.78/1.19  tff(c_119, plain, (![A_1]: (r1_tarski(A_1, '#skF_2') | ~r1_tarski(A_1, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_106, c_2])).
% 1.78/1.19  tff(c_12, plain, (![B_11, A_10]: (k1_tarski(B_11)=A_10 | k1_xboole_0=A_10 | ~r1_tarski(A_10, k1_tarski(B_11)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.78/1.19  tff(c_111, plain, (![A_10]: (k1_tarski('#skF_1')=A_10 | k1_xboole_0=A_10 | ~r1_tarski(A_10, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_102, c_12])).
% 1.78/1.19  tff(c_129, plain, (![A_30]: (A_30='#skF_2' | k1_xboole_0=A_30 | ~r1_tarski(A_30, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_102, c_111])).
% 1.78/1.19  tff(c_150, plain, (![A_31]: (A_31='#skF_2' | k1_xboole_0=A_31 | ~r1_tarski(A_31, '#skF_3'))), inference(resolution, [status(thm)], [c_119, c_129])).
% 1.78/1.19  tff(c_158, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_48, c_150])).
% 1.78/1.19  tff(c_166, plain, $false, inference(negUnitSimplification, [status(thm)], [c_18, c_22, c_158])).
% 1.78/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.78/1.19  
% 1.78/1.19  Inference rules
% 1.78/1.19  ----------------------
% 1.78/1.19  #Ref     : 0
% 1.78/1.19  #Sup     : 29
% 1.78/1.19  #Fact    : 0
% 1.78/1.19  #Define  : 0
% 1.78/1.19  #Split   : 0
% 1.78/1.19  #Chain   : 0
% 1.78/1.19  #Close   : 0
% 1.78/1.19  
% 1.78/1.19  Ordering : KBO
% 1.78/1.19  
% 1.78/1.19  Simplification rules
% 1.78/1.19  ----------------------
% 1.78/1.19  #Subsume      : 1
% 1.78/1.19  #Demod        : 9
% 1.78/1.19  #Tautology    : 22
% 1.78/1.19  #SimpNegUnit  : 5
% 1.78/1.19  #BackRed      : 2
% 1.78/1.19  
% 1.78/1.19  #Partial instantiations: 0
% 1.78/1.19  #Strategies tried      : 1
% 1.78/1.19  
% 1.78/1.19  Timing (in seconds)
% 1.78/1.19  ----------------------
% 1.78/1.19  Preprocessing        : 0.26
% 1.78/1.19  Parsing              : 0.14
% 1.78/1.19  CNF conversion       : 0.02
% 1.78/1.19  Main loop            : 0.12
% 1.78/1.19  Inferencing          : 0.04
% 1.78/1.19  Reduction            : 0.04
% 1.78/1.19  Demodulation         : 0.03
% 1.78/1.19  BG Simplification    : 0.01
% 1.78/1.19  Subsumption          : 0.02
% 1.78/1.19  Abstraction          : 0.01
% 1.78/1.19  MUC search           : 0.00
% 1.78/1.19  Cooper               : 0.00
% 1.78/1.19  Total                : 0.40
% 1.78/1.19  Index Insertion      : 0.00
% 1.78/1.19  Index Deletion       : 0.00
% 1.78/1.19  Index Matching       : 0.00
% 1.78/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

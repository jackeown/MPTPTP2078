%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:51 EST 2020

% Result     : Theorem 1.95s
% Output     : CNFRefutation 1.95s
% Verified   : 
% Statistics : Number of formulae       :   25 (  29 expanded)
%              Number of leaves         :   14 (  17 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  46 expanded)
%              Number of equality atoms :   31 (  39 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(c_20,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_22,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( r1_tarski(A_1,B_2)
      | k4_xboole_0(A_1,B_2) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3] : k2_tarski(A_3,A_3) = k1_tarski(A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_113,plain,(
    ! [B_26,C_27,A_28] :
      ( k2_tarski(B_26,C_27) = A_28
      | k1_tarski(C_27) = A_28
      | k1_tarski(B_26) = A_28
      | k1_xboole_0 = A_28
      | ~ r1_tarski(A_28,k2_tarski(B_26,C_27)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_129,plain,(
    ! [A_3,A_28] :
      ( k2_tarski(A_3,A_3) = A_28
      | k1_tarski(A_3) = A_28
      | k1_tarski(A_3) = A_28
      | k1_xboole_0 = A_28
      | ~ r1_tarski(A_28,k1_tarski(A_3)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_113])).

tff(c_213,plain,(
    ! [A_38,A_39] :
      ( k1_tarski(A_38) = A_39
      | k1_tarski(A_38) = A_39
      | k1_tarski(A_38) = A_39
      | k1_xboole_0 = A_39
      | ~ r1_tarski(A_39,k1_tarski(A_38)) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_129])).

tff(c_229,plain,(
    ! [A_40,A_41] :
      ( k1_tarski(A_40) = A_41
      | k1_xboole_0 = A_41
      | k4_xboole_0(A_41,k1_tarski(A_40)) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_2,c_213])).

tff(c_238,plain,
    ( k1_tarski('#skF_2') = '#skF_1'
    | k1_xboole_0 = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_229])).

tff(c_246,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_20,c_18,c_238])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.14/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:30:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.95/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.23  
% 1.95/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.23  %$ r1_tarski > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.95/1.23  
% 1.95/1.23  %Foreground sorts:
% 1.95/1.23  
% 1.95/1.23  
% 1.95/1.23  %Background operators:
% 1.95/1.23  
% 1.95/1.23  
% 1.95/1.23  %Foreground operators:
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.95/1.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.95/1.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.95/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.95/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.95/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.95/1.23  tff('#skF_2', type, '#skF_2': $i).
% 1.95/1.23  tff('#skF_1', type, '#skF_1': $i).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.95/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.95/1.23  
% 1.95/1.24  tff(f_56, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 1.95/1.24  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 1.95/1.24  tff(f_31, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.95/1.24  tff(f_46, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 1.95/1.24  tff(c_20, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.95/1.24  tff(c_18, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.95/1.24  tff(c_22, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.95/1.24  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(A_1, B_2) | k4_xboole_0(A_1, B_2)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.95/1.24  tff(c_6, plain, (![A_3]: (k2_tarski(A_3, A_3)=k1_tarski(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.95/1.24  tff(c_113, plain, (![B_26, C_27, A_28]: (k2_tarski(B_26, C_27)=A_28 | k1_tarski(C_27)=A_28 | k1_tarski(B_26)=A_28 | k1_xboole_0=A_28 | ~r1_tarski(A_28, k2_tarski(B_26, C_27)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.95/1.24  tff(c_129, plain, (![A_3, A_28]: (k2_tarski(A_3, A_3)=A_28 | k1_tarski(A_3)=A_28 | k1_tarski(A_3)=A_28 | k1_xboole_0=A_28 | ~r1_tarski(A_28, k1_tarski(A_3)))), inference(superposition, [status(thm), theory('equality')], [c_6, c_113])).
% 1.95/1.24  tff(c_213, plain, (![A_38, A_39]: (k1_tarski(A_38)=A_39 | k1_tarski(A_38)=A_39 | k1_tarski(A_38)=A_39 | k1_xboole_0=A_39 | ~r1_tarski(A_39, k1_tarski(A_38)))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_129])).
% 1.95/1.24  tff(c_229, plain, (![A_40, A_41]: (k1_tarski(A_40)=A_41 | k1_xboole_0=A_41 | k4_xboole_0(A_41, k1_tarski(A_40))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_2, c_213])).
% 1.95/1.24  tff(c_238, plain, (k1_tarski('#skF_2')='#skF_1' | k1_xboole_0='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_22, c_229])).
% 1.95/1.24  tff(c_246, plain, $false, inference(negUnitSimplification, [status(thm)], [c_20, c_18, c_238])).
% 1.95/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.95/1.24  
% 1.95/1.24  Inference rules
% 1.95/1.24  ----------------------
% 1.95/1.24  #Ref     : 0
% 1.95/1.24  #Sup     : 52
% 1.95/1.24  #Fact    : 0
% 1.95/1.24  #Define  : 0
% 1.95/1.24  #Split   : 0
% 1.95/1.24  #Chain   : 0
% 1.95/1.24  #Close   : 0
% 1.95/1.24  
% 1.95/1.24  Ordering : KBO
% 1.95/1.24  
% 1.95/1.24  Simplification rules
% 1.95/1.24  ----------------------
% 1.95/1.24  #Subsume      : 0
% 1.95/1.24  #Demod        : 14
% 1.95/1.24  #Tautology    : 39
% 1.95/1.24  #SimpNegUnit  : 1
% 1.95/1.24  #BackRed      : 0
% 1.95/1.24  
% 1.95/1.24  #Partial instantiations: 0
% 1.95/1.24  #Strategies tried      : 1
% 1.95/1.24  
% 1.95/1.24  Timing (in seconds)
% 1.95/1.24  ----------------------
% 1.95/1.24  Preprocessing        : 0.26
% 1.95/1.24  Parsing              : 0.13
% 1.95/1.24  CNF conversion       : 0.02
% 1.95/1.24  Main loop            : 0.17
% 1.95/1.24  Inferencing          : 0.07
% 1.95/1.24  Reduction            : 0.05
% 1.95/1.24  Demodulation         : 0.04
% 1.95/1.24  BG Simplification    : 0.01
% 1.95/1.24  Subsumption          : 0.03
% 1.95/1.24  Abstraction          : 0.01
% 1.95/1.24  MUC search           : 0.00
% 1.95/1.24  Cooper               : 0.00
% 1.95/1.24  Total                : 0.45
% 1.95/1.24  Index Insertion      : 0.00
% 1.95/1.24  Index Deletion       : 0.00
% 1.95/1.24  Index Matching       : 0.00
% 1.95/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------

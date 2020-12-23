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

% Result     : Theorem 1.69s
% Output     : CNFRefutation 1.69s
% Verified   : 
% Statistics : Number of formulae       :   37 (  39 expanded)
%              Number of leaves         :   21 (  23 expanded)
%              Depth                    :    6
%              Number of atoms          :   35 (  41 expanded)
%              Number of equality atoms :   34 (  40 expanded)
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

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ~ ( k4_xboole_0(A,k1_tarski(B)) = k1_xboole_0
          & A != k1_xboole_0
          & A != k1_tarski(B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B] : k4_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_29,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_56,axiom,(
    ! [A,B,C] :
      ~ ( k1_tarski(A) = k2_xboole_0(B,C)
        & B != C
        & B != k1_xboole_0
        & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(c_22,plain,(
    k1_tarski('#skF_2') != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_8,plain,(
    ! [A_6] : k2_tarski(A_6,A_6) = k1_tarski(A_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    ! [A_24,B_25] : k4_xboole_0(k1_tarski(A_24),k2_tarski(A_24,B_25)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_66,plain,(
    ! [A_6] : k4_xboole_0(k1_tarski(A_6),k1_tarski(A_6)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_59])).

tff(c_14,plain,(
    ! [B_13] : k4_xboole_0(k1_tarski(B_13),k1_tarski(B_13)) != k1_tarski(B_13) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_69,plain,(
    ! [B_13] : k1_tarski(B_13) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_14])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_26,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_77,plain,(
    ! [A_27,B_28] : k5_xboole_0(A_27,k4_xboole_0(B_28,A_27)) = k2_xboole_0(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_92,plain,(
    k5_xboole_0(k1_tarski('#skF_2'),k1_xboole_0) = k2_xboole_0(k1_tarski('#skF_2'),'#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_77])).

tff(c_97,plain,(
    k2_xboole_0(k1_tarski('#skF_2'),'#skF_1') = k1_tarski('#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_92])).

tff(c_167,plain,(
    ! [C_40,B_41,A_42] :
      ( k1_xboole_0 = C_40
      | k1_xboole_0 = B_41
      | C_40 = B_41
      | k2_xboole_0(B_41,C_40) != k1_tarski(A_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_176,plain,(
    ! [A_42] :
      ( k1_xboole_0 = '#skF_1'
      | k1_tarski('#skF_2') = k1_xboole_0
      | k1_tarski('#skF_2') = '#skF_1'
      | k1_tarski(A_42) != k1_tarski('#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_167])).

tff(c_180,plain,(
    ! [A_42] : k1_tarski(A_42) != k1_tarski('#skF_2') ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_69,c_24,c_176])).

tff(c_184,plain,(
    $false ),
    inference(reflexivity,[status(thm),theory(equality)],[c_180])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:45:32 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.69/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.14  
% 1.69/1.14  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.14  %$ k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.69/1.14  
% 1.69/1.14  %Foreground sorts:
% 1.69/1.14  
% 1.69/1.14  
% 1.69/1.14  %Background operators:
% 1.69/1.14  
% 1.69/1.14  
% 1.69/1.14  %Foreground operators:
% 1.69/1.14  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.69/1.14  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.69/1.14  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.69/1.14  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.69/1.14  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.69/1.14  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.69/1.14  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.69/1.14  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.69/1.14  tff('#skF_2', type, '#skF_2': $i).
% 1.69/1.14  tff('#skF_1', type, '#skF_1': $i).
% 1.69/1.14  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.69/1.14  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.69/1.14  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.69/1.14  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.69/1.14  
% 1.69/1.15  tff(f_66, negated_conjecture, ~(![A, B]: ~(((k4_xboole_0(A, k1_tarski(B)) = k1_xboole_0) & ~(A = k1_xboole_0)) & ~(A = k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_zfmisc_1)).
% 1.69/1.15  tff(f_33, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.69/1.15  tff(f_44, axiom, (![A, B]: (k4_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_zfmisc_1)).
% 1.69/1.15  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.69/1.15  tff(f_29, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.69/1.15  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 1.69/1.15  tff(f_56, axiom, (![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 1.69/1.15  tff(c_22, plain, (k1_tarski('#skF_2')!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.69/1.15  tff(c_8, plain, (![A_6]: (k2_tarski(A_6, A_6)=k1_tarski(A_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.69/1.15  tff(c_59, plain, (![A_24, B_25]: (k4_xboole_0(k1_tarski(A_24), k2_tarski(A_24, B_25))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.69/1.15  tff(c_66, plain, (![A_6]: (k4_xboole_0(k1_tarski(A_6), k1_tarski(A_6))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_8, c_59])).
% 1.69/1.15  tff(c_14, plain, (![B_13]: (k4_xboole_0(k1_tarski(B_13), k1_tarski(B_13))!=k1_tarski(B_13))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.69/1.15  tff(c_69, plain, (![B_13]: (k1_tarski(B_13)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_66, c_14])).
% 1.69/1.15  tff(c_24, plain, (k1_xboole_0!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.69/1.15  tff(c_4, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.69/1.15  tff(c_26, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_66])).
% 1.69/1.15  tff(c_77, plain, (![A_27, B_28]: (k5_xboole_0(A_27, k4_xboole_0(B_28, A_27))=k2_xboole_0(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.69/1.15  tff(c_92, plain, (k5_xboole_0(k1_tarski('#skF_2'), k1_xboole_0)=k2_xboole_0(k1_tarski('#skF_2'), '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_26, c_77])).
% 1.69/1.15  tff(c_97, plain, (k2_xboole_0(k1_tarski('#skF_2'), '#skF_1')=k1_tarski('#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_4, c_92])).
% 1.69/1.15  tff(c_167, plain, (![C_40, B_41, A_42]: (k1_xboole_0=C_40 | k1_xboole_0=B_41 | C_40=B_41 | k2_xboole_0(B_41, C_40)!=k1_tarski(A_42))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.69/1.15  tff(c_176, plain, (![A_42]: (k1_xboole_0='#skF_1' | k1_tarski('#skF_2')=k1_xboole_0 | k1_tarski('#skF_2')='#skF_1' | k1_tarski(A_42)!=k1_tarski('#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_97, c_167])).
% 1.69/1.15  tff(c_180, plain, (![A_42]: (k1_tarski(A_42)!=k1_tarski('#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_22, c_69, c_24, c_176])).
% 1.69/1.15  tff(c_184, plain, $false, inference(reflexivity, [status(thm), theory('equality')], [c_180])).
% 1.69/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.69/1.15  
% 1.69/1.15  Inference rules
% 1.69/1.15  ----------------------
% 1.69/1.15  #Ref     : 1
% 1.69/1.15  #Sup     : 37
% 1.69/1.15  #Fact    : 0
% 1.69/1.15  #Define  : 0
% 1.69/1.15  #Split   : 0
% 1.69/1.15  #Chain   : 0
% 1.69/1.15  #Close   : 0
% 1.69/1.15  
% 1.69/1.15  Ordering : KBO
% 1.69/1.15  
% 1.69/1.15  Simplification rules
% 1.69/1.15  ----------------------
% 1.69/1.15  #Subsume      : 0
% 1.69/1.15  #Demod        : 6
% 1.69/1.15  #Tautology    : 30
% 1.69/1.15  #SimpNegUnit  : 5
% 1.69/1.15  #BackRed      : 1
% 1.69/1.15  
% 1.69/1.15  #Partial instantiations: 0
% 1.69/1.15  #Strategies tried      : 1
% 1.69/1.15  
% 1.69/1.15  Timing (in seconds)
% 1.69/1.15  ----------------------
% 1.69/1.15  Preprocessing        : 0.28
% 1.69/1.15  Parsing              : 0.14
% 1.69/1.15  CNF conversion       : 0.02
% 1.69/1.15  Main loop            : 0.12
% 1.69/1.15  Inferencing          : 0.05
% 1.69/1.15  Reduction            : 0.04
% 1.69/1.15  Demodulation         : 0.03
% 1.69/1.15  BG Simplification    : 0.01
% 1.69/1.15  Subsumption          : 0.01
% 1.69/1.15  Abstraction          : 0.01
% 1.69/1.15  MUC search           : 0.00
% 1.69/1.15  Cooper               : 0.00
% 1.69/1.15  Total                : 0.42
% 1.69/1.15  Index Insertion      : 0.00
% 1.69/1.15  Index Deletion       : 0.00
% 1.69/1.15  Index Matching       : 0.00
% 1.69/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

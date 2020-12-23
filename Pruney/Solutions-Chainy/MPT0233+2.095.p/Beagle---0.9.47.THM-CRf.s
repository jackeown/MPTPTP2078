%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:33 EST 2020

% Result     : Theorem 2.33s
% Output     : CNFRefutation 2.50s
% Verified   : 
% Statistics : Number of formulae       :   37 (  39 expanded)
%              Number of leaves         :   23 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  40 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_76,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C] :
      ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
        & A != B
        & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(c_34,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_32,plain,(
    '#skF_1' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_123,plain,(
    ! [A_55,B_56] : k3_xboole_0(k1_tarski(A_55),k2_tarski(A_55,B_56)) = k1_tarski(A_55) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_49,plain,(
    ! [B_47,A_48] : k3_xboole_0(B_47,A_48) = k3_xboole_0(A_48,B_47) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_5,B_6] : r1_tarski(k3_xboole_0(A_5,B_6),A_5) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_64,plain,(
    ! [B_47,A_48] : r1_tarski(k3_xboole_0(B_47,A_48),A_48) ),
    inference(superposition,[status(thm),theory(equality)],[c_49,c_10])).

tff(c_129,plain,(
    ! [A_55,B_56] : r1_tarski(k1_tarski(A_55),k2_tarski(A_55,B_56)) ),
    inference(superposition,[status(thm),theory(equality)],[c_123,c_64])).

tff(c_36,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k2_tarski('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_176,plain,(
    ! [A_63,C_64,B_65] :
      ( r1_tarski(A_63,C_64)
      | ~ r1_tarski(B_65,C_64)
      | ~ r1_tarski(A_63,B_65) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_188,plain,(
    ! [A_63] :
      ( r1_tarski(A_63,k2_tarski('#skF_3','#skF_4'))
      | ~ r1_tarski(A_63,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_36,c_176])).

tff(c_373,plain,(
    ! [C_82,A_83,B_84] :
      ( C_82 = A_83
      | B_84 = A_83
      | ~ r1_tarski(k1_tarski(A_83),k2_tarski(B_84,C_82)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_505,plain,(
    ! [A_98] :
      ( A_98 = '#skF_4'
      | A_98 = '#skF_3'
      | ~ r1_tarski(k1_tarski(A_98),k2_tarski('#skF_1','#skF_2')) ) ),
    inference(resolution,[status(thm)],[c_188,c_373])).

tff(c_509,plain,
    ( '#skF_1' = '#skF_4'
    | '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_129,c_505])).

tff(c_513,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_509])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:16:37 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.21/0.47  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.33/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.45  
% 2.33/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.33/1.46  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.33/1.46  
% 2.33/1.46  %Foreground sorts:
% 2.33/1.46  
% 2.33/1.46  
% 2.33/1.46  %Background operators:
% 2.33/1.46  
% 2.33/1.46  
% 2.33/1.46  %Foreground operators:
% 2.33/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.33/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.33/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.33/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.33/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.33/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.33/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.33/1.46  tff('#skF_2', type, '#skF_2': $i).
% 2.33/1.46  tff('#skF_3', type, '#skF_3': $i).
% 2.33/1.46  tff('#skF_1', type, '#skF_1': $i).
% 2.33/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.33/1.46  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.33/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.33/1.46  tff('#skF_4', type, '#skF_4': $i).
% 2.33/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.33/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.33/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.33/1.46  
% 2.50/1.46  tff(f_76, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 2.50/1.46  tff(f_57, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.50/1.46  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.50/1.46  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 2.50/1.46  tff(f_41, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 2.50/1.46  tff(f_66, axiom, (![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.50/1.46  tff(c_34, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.50/1.46  tff(c_32, plain, ('#skF_1'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.50/1.46  tff(c_123, plain, (![A_55, B_56]: (k3_xboole_0(k1_tarski(A_55), k2_tarski(A_55, B_56))=k1_tarski(A_55))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.50/1.46  tff(c_49, plain, (![B_47, A_48]: (k3_xboole_0(B_47, A_48)=k3_xboole_0(A_48, B_47))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.50/1.46  tff(c_10, plain, (![A_5, B_6]: (r1_tarski(k3_xboole_0(A_5, B_6), A_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.50/1.46  tff(c_64, plain, (![B_47, A_48]: (r1_tarski(k3_xboole_0(B_47, A_48), A_48))), inference(superposition, [status(thm), theory('equality')], [c_49, c_10])).
% 2.50/1.46  tff(c_129, plain, (![A_55, B_56]: (r1_tarski(k1_tarski(A_55), k2_tarski(A_55, B_56)))), inference(superposition, [status(thm), theory('equality')], [c_123, c_64])).
% 2.50/1.46  tff(c_36, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k2_tarski('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.50/1.46  tff(c_176, plain, (![A_63, C_64, B_65]: (r1_tarski(A_63, C_64) | ~r1_tarski(B_65, C_64) | ~r1_tarski(A_63, B_65))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.50/1.46  tff(c_188, plain, (![A_63]: (r1_tarski(A_63, k2_tarski('#skF_3', '#skF_4')) | ~r1_tarski(A_63, k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_36, c_176])).
% 2.50/1.46  tff(c_373, plain, (![C_82, A_83, B_84]: (C_82=A_83 | B_84=A_83 | ~r1_tarski(k1_tarski(A_83), k2_tarski(B_84, C_82)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.50/1.46  tff(c_505, plain, (![A_98]: (A_98='#skF_4' | A_98='#skF_3' | ~r1_tarski(k1_tarski(A_98), k2_tarski('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_188, c_373])).
% 2.50/1.46  tff(c_509, plain, ('#skF_1'='#skF_4' | '#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_129, c_505])).
% 2.50/1.46  tff(c_513, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_509])).
% 2.50/1.46  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.50/1.46  
% 2.50/1.46  Inference rules
% 2.50/1.46  ----------------------
% 2.50/1.46  #Ref     : 0
% 2.50/1.46  #Sup     : 113
% 2.50/1.46  #Fact    : 0
% 2.50/1.46  #Define  : 0
% 2.50/1.46  #Split   : 1
% 2.50/1.46  #Chain   : 0
% 2.50/1.46  #Close   : 0
% 2.50/1.46  
% 2.50/1.46  Ordering : KBO
% 2.50/1.46  
% 2.50/1.46  Simplification rules
% 2.50/1.46  ----------------------
% 2.50/1.46  #Subsume      : 4
% 2.50/1.47  #Demod        : 42
% 2.50/1.47  #Tautology    : 67
% 2.50/1.47  #SimpNegUnit  : 1
% 2.50/1.47  #BackRed      : 0
% 2.50/1.47  
% 2.50/1.47  #Partial instantiations: 0
% 2.50/1.47  #Strategies tried      : 1
% 2.50/1.47  
% 2.50/1.47  Timing (in seconds)
% 2.50/1.47  ----------------------
% 2.50/1.47  Preprocessing        : 0.32
% 2.50/1.47  Parsing              : 0.16
% 2.50/1.47  CNF conversion       : 0.02
% 2.50/1.47  Main loop            : 0.26
% 2.50/1.47  Inferencing          : 0.08
% 2.50/1.47  Reduction            : 0.09
% 2.50/1.47  Demodulation         : 0.07
% 2.50/1.47  BG Simplification    : 0.02
% 2.50/1.47  Subsumption          : 0.05
% 2.50/1.47  Abstraction          : 0.01
% 2.50/1.47  MUC search           : 0.00
% 2.50/1.47  Cooper               : 0.00
% 2.50/1.47  Total                : 0.60
% 2.50/1.47  Index Insertion      : 0.00
% 2.50/1.47  Index Deletion       : 0.00
% 2.50/1.47  Index Matching       : 0.00
% 2.50/1.47  BG Taut test         : 0.00
%------------------------------------------------------------------------------

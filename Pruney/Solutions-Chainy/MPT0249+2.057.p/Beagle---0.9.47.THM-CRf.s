%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n003.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:31 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   37 (  45 expanded)
%              Number of leaves         :   19 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   39 (  63 expanded)
%              Number of equality atoms :   23 (  44 expanded)
%              Maximal formula depth    :   10 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_60,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & B != C
          & B != k1_xboole_0
          & C != k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t44_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(c_22,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_26,plain,(
    '#skF_2' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_40,plain,(
    ! [A_21,B_22] : r1_tarski(A_21,k2_xboole_0(A_21,B_22)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_43,plain,(
    ! [A_1] : r1_tarski(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_40])).

tff(c_24,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_28,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_49,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_6])).

tff(c_110,plain,(
    ! [B_37,A_38] :
      ( k1_tarski(B_37) = A_38
      | k1_xboole_0 = A_38
      | ~ r1_tarski(A_38,k1_tarski(B_37)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_116,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_49,c_110])).

tff(c_127,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_116])).

tff(c_93,plain,(
    ! [A_30,C_31,B_32] :
      ( r1_tarski(A_30,k2_xboole_0(C_31,B_32))
      | ~ r1_tarski(A_30,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_96,plain,(
    ! [A_30] :
      ( r1_tarski(A_30,k1_tarski('#skF_1'))
      | ~ r1_tarski(A_30,'#skF_3') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_93])).

tff(c_124,plain,(
    ! [A_30] :
      ( k1_tarski('#skF_1') = A_30
      | k1_xboole_0 = A_30
      | ~ r1_tarski(A_30,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_96,c_110])).

tff(c_186,plain,(
    ! [A_41] :
      ( A_41 = '#skF_2'
      | k1_xboole_0 = A_41
      | ~ r1_tarski(A_41,'#skF_3') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_127,c_124])).

tff(c_190,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_43,c_186])).

tff(c_194,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_26,c_190])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n003.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 14:42:12 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.15  
% 1.79/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.79/1.15  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 1.79/1.15  
% 1.79/1.15  %Foreground sorts:
% 1.79/1.15  
% 1.79/1.15  
% 1.79/1.15  %Background operators:
% 1.79/1.15  
% 1.79/1.15  
% 1.79/1.15  %Foreground operators:
% 1.79/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.79/1.15  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.79/1.15  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.15  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.79/1.15  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.79/1.15  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.79/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.79/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.15  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.79/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.79/1.15  
% 1.85/1.16  tff(f_60, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~(B = C)) & ~(B = k1_xboole_0)) & ~(C = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t44_zfmisc_1)).
% 1.85/1.16  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 1.85/1.16  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.85/1.16  tff(f_45, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 1.85/1.16  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 1.85/1.16  tff(c_22, plain, (k1_xboole_0!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.16  tff(c_26, plain, ('#skF_2'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.16  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.85/1.16  tff(c_40, plain, (![A_21, B_22]: (r1_tarski(A_21, k2_xboole_0(A_21, B_22)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.85/1.16  tff(c_43, plain, (![A_1]: (r1_tarski(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_40])).
% 1.85/1.16  tff(c_24, plain, (k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.16  tff(c_28, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.16  tff(c_6, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.85/1.16  tff(c_49, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_6])).
% 1.85/1.16  tff(c_110, plain, (![B_37, A_38]: (k1_tarski(B_37)=A_38 | k1_xboole_0=A_38 | ~r1_tarski(A_38, k1_tarski(B_37)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.85/1.16  tff(c_116, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_49, c_110])).
% 1.85/1.16  tff(c_127, plain, (k1_tarski('#skF_1')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_24, c_116])).
% 1.85/1.16  tff(c_93, plain, (![A_30, C_31, B_32]: (r1_tarski(A_30, k2_xboole_0(C_31, B_32)) | ~r1_tarski(A_30, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.16  tff(c_96, plain, (![A_30]: (r1_tarski(A_30, k1_tarski('#skF_1')) | ~r1_tarski(A_30, '#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_28, c_93])).
% 1.85/1.16  tff(c_124, plain, (![A_30]: (k1_tarski('#skF_1')=A_30 | k1_xboole_0=A_30 | ~r1_tarski(A_30, '#skF_3'))), inference(resolution, [status(thm)], [c_96, c_110])).
% 1.85/1.16  tff(c_186, plain, (![A_41]: (A_41='#skF_2' | k1_xboole_0=A_41 | ~r1_tarski(A_41, '#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_127, c_124])).
% 1.85/1.16  tff(c_190, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_43, c_186])).
% 1.85/1.16  tff(c_194, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_26, c_190])).
% 1.85/1.16  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.16  
% 1.85/1.16  Inference rules
% 1.85/1.16  ----------------------
% 1.85/1.16  #Ref     : 0
% 1.85/1.16  #Sup     : 38
% 1.85/1.16  #Fact    : 0
% 1.85/1.16  #Define  : 0
% 1.85/1.16  #Split   : 0
% 1.85/1.16  #Chain   : 0
% 1.85/1.16  #Close   : 0
% 1.85/1.16  
% 1.85/1.16  Ordering : KBO
% 1.85/1.16  
% 1.85/1.16  Simplification rules
% 1.85/1.16  ----------------------
% 1.85/1.16  #Subsume      : 1
% 1.85/1.16  #Demod        : 9
% 1.85/1.16  #Tautology    : 28
% 1.85/1.16  #SimpNegUnit  : 4
% 1.85/1.16  #BackRed      : 3
% 1.85/1.16  
% 1.85/1.16  #Partial instantiations: 0
% 1.85/1.16  #Strategies tried      : 1
% 1.85/1.16  
% 1.85/1.16  Timing (in seconds)
% 1.85/1.16  ----------------------
% 1.85/1.17  Preprocessing        : 0.27
% 1.85/1.17  Parsing              : 0.14
% 1.85/1.17  CNF conversion       : 0.02
% 1.85/1.17  Main loop            : 0.13
% 1.85/1.17  Inferencing          : 0.05
% 1.85/1.17  Reduction            : 0.04
% 1.85/1.17  Demodulation         : 0.03
% 1.85/1.17  BG Simplification    : 0.01
% 1.85/1.17  Subsumption          : 0.02
% 1.85/1.17  Abstraction          : 0.01
% 1.85/1.17  MUC search           : 0.00
% 1.85/1.17  Cooper               : 0.00
% 1.85/1.17  Total                : 0.43
% 1.85/1.17  Index Insertion      : 0.00
% 1.85/1.17  Index Deletion       : 0.00
% 1.85/1.17  Index Matching       : 0.00
% 1.85/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:19 EST 2020

% Result     : Theorem 1.73s
% Output     : CNFRefutation 1.73s
% Verified   : 
% Statistics : Number of formulae       :   31 (  32 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   24 (  26 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => A = C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t26_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_xboole_0(A,B),C)
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t11_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_22,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_24,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_18,plain,(
    ! [A_27,B_28] : r1_tarski(k1_tarski(A_27),k2_tarski(A_27,B_28)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_39,plain,(
    ! [A_35,B_36] :
      ( k2_xboole_0(A_35,B_36) = B_36
      | ~ r1_tarski(A_35,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_96,plain,(
    ! [A_48,B_49] : k2_xboole_0(k1_tarski(A_48),k2_tarski(A_48,B_49)) = k2_tarski(A_48,B_49) ),
    inference(resolution,[status(thm)],[c_18,c_39])).

tff(c_2,plain,(
    ! [A_1,C_3,B_2] :
      ( r1_tarski(A_1,C_3)
      | ~ r1_tarski(k2_xboole_0(A_1,B_2),C_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_117,plain,(
    ! [A_51,C_52,B_53] :
      ( r1_tarski(k1_tarski(A_51),C_52)
      | ~ r1_tarski(k2_tarski(A_51,B_53),C_52) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_96,c_2])).

tff(c_128,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_24,c_117])).

tff(c_20,plain,(
    ! [B_30,A_29] :
      ( B_30 = A_29
      | ~ r1_tarski(k1_tarski(A_29),k1_tarski(B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_140,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_128,c_20])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:06:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.73/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.16  
% 1.73/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.16  %$ r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.73/1.16  
% 1.73/1.16  %Foreground sorts:
% 1.73/1.16  
% 1.73/1.16  
% 1.73/1.16  %Background operators:
% 1.73/1.16  
% 1.73/1.16  
% 1.73/1.16  %Foreground operators:
% 1.73/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.73/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.73/1.16  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.73/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.73/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.73/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.73/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.73/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.73/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.73/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.73/1.16  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.73/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.73/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.73/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.73/1.16  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.73/1.16  
% 1.73/1.17  tff(f_56, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t26_zfmisc_1)).
% 1.73/1.17  tff(f_47, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 1.73/1.17  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 1.73/1.17  tff(f_29, axiom, (![A, B, C]: (r1_tarski(k2_xboole_0(A, B), C) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t11_xboole_1)).
% 1.73/1.17  tff(f_51, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.73/1.17  tff(c_22, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.73/1.17  tff(c_24, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 1.73/1.17  tff(c_18, plain, (![A_27, B_28]: (r1_tarski(k1_tarski(A_27), k2_tarski(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 1.73/1.17  tff(c_39, plain, (![A_35, B_36]: (k2_xboole_0(A_35, B_36)=B_36 | ~r1_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.73/1.17  tff(c_96, plain, (![A_48, B_49]: (k2_xboole_0(k1_tarski(A_48), k2_tarski(A_48, B_49))=k2_tarski(A_48, B_49))), inference(resolution, [status(thm)], [c_18, c_39])).
% 1.73/1.17  tff(c_2, plain, (![A_1, C_3, B_2]: (r1_tarski(A_1, C_3) | ~r1_tarski(k2_xboole_0(A_1, B_2), C_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.73/1.17  tff(c_117, plain, (![A_51, C_52, B_53]: (r1_tarski(k1_tarski(A_51), C_52) | ~r1_tarski(k2_tarski(A_51, B_53), C_52))), inference(superposition, [status(thm), theory('equality')], [c_96, c_2])).
% 1.73/1.17  tff(c_128, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_24, c_117])).
% 1.73/1.17  tff(c_20, plain, (![B_30, A_29]: (B_30=A_29 | ~r1_tarski(k1_tarski(A_29), k1_tarski(B_30)))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.73/1.17  tff(c_140, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_128, c_20])).
% 1.73/1.17  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_140])).
% 1.73/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.73/1.17  
% 1.73/1.17  Inference rules
% 1.73/1.17  ----------------------
% 1.73/1.17  #Ref     : 0
% 1.73/1.17  #Sup     : 29
% 1.73/1.17  #Fact    : 0
% 1.73/1.17  #Define  : 0
% 1.73/1.17  #Split   : 0
% 1.73/1.17  #Chain   : 0
% 1.73/1.17  #Close   : 0
% 1.73/1.17  
% 1.73/1.17  Ordering : KBO
% 1.73/1.17  
% 1.73/1.17  Simplification rules
% 1.73/1.17  ----------------------
% 1.73/1.17  #Subsume      : 0
% 1.73/1.17  #Demod        : 2
% 1.73/1.17  #Tautology    : 18
% 1.73/1.17  #SimpNegUnit  : 1
% 1.73/1.17  #BackRed      : 0
% 1.73/1.17  
% 1.73/1.17  #Partial instantiations: 0
% 1.73/1.17  #Strategies tried      : 1
% 1.73/1.17  
% 1.73/1.17  Timing (in seconds)
% 1.73/1.17  ----------------------
% 1.73/1.17  Preprocessing        : 0.30
% 1.73/1.17  Parsing              : 0.16
% 1.73/1.17  CNF conversion       : 0.02
% 1.73/1.17  Main loop            : 0.12
% 1.73/1.17  Inferencing          : 0.05
% 1.73/1.17  Reduction            : 0.04
% 1.73/1.17  Demodulation         : 0.03
% 1.73/1.17  BG Simplification    : 0.01
% 1.73/1.17  Subsumption          : 0.02
% 1.73/1.17  Abstraction          : 0.01
% 1.73/1.17  MUC search           : 0.00
% 1.73/1.17  Cooper               : 0.00
% 1.73/1.17  Total                : 0.43
% 1.73/1.17  Index Insertion      : 0.00
% 1.73/1.18  Index Deletion       : 0.00
% 1.73/1.18  Index Matching       : 0.00
% 1.73/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

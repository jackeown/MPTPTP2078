%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:20 EST 2020

% Result     : Theorem 2.14s
% Output     : CNFRefutation 2.14s
% Verified   : 
% Statistics : Number of formulae       :   36 (  41 expanded)
%              Number of leaves         :   19 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   38 (  45 expanded)
%              Number of equality atoms :   13 (  15 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_49,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(c_20,plain,(
    ! [A_16,B_17] : r1_tarski(k1_tarski(A_16),k2_tarski(A_16,B_17)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_26,plain,(
    r1_tarski(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_79,plain,(
    ! [A_28,B_29] :
      ( k2_xboole_0(A_28,B_29) = B_29
      | ~ r1_tarski(A_28,B_29) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_89,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_2'),k1_tarski('#skF_3')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_26,c_79])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_147,plain,(
    ! [A_34,C_35,B_36] :
      ( r1_tarski(A_34,k2_xboole_0(C_35,B_36))
      | ~ r1_tarski(A_34,B_36) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_191,plain,(
    ! [A_42,A_43,B_44] :
      ( r1_tarski(A_42,k2_xboole_0(A_43,B_44))
      | ~ r1_tarski(A_42,A_43) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_147])).

tff(c_243,plain,(
    ! [A_47] :
      ( r1_tarski(A_47,k1_tarski('#skF_3'))
      | ~ r1_tarski(A_47,k2_tarski('#skF_1','#skF_2')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_89,c_191])).

tff(c_252,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(resolution,[status(thm)],[c_20,c_243])).

tff(c_22,plain,(
    ! [B_19,A_18] :
      ( B_19 = A_18
      | ~ r1_tarski(k1_tarski(A_18),k1_tarski(B_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_332,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_252,c_22])).

tff(c_24,plain,(
    k2_tarski('#skF_1','#skF_2') != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_164,plain,(
    ! [B_37,A_38] :
      ( B_37 = A_38
      | ~ r1_tarski(B_37,A_38)
      | ~ r1_tarski(A_38,B_37) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_168,plain,
    ( k2_tarski('#skF_1','#skF_2') = k1_tarski('#skF_3')
    | ~ r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_26,c_164])).

tff(c_176,plain,(
    ~ r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_1','#skF_2')) ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_168])).

tff(c_336,plain,(
    ~ r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_176])).

tff(c_343,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_336])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:11:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.14/1.31  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.31  
% 2.14/1.31  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.31  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 2.14/1.31  
% 2.14/1.31  %Foreground sorts:
% 2.14/1.31  
% 2.14/1.31  
% 2.14/1.31  %Background operators:
% 2.14/1.31  
% 2.14/1.31  
% 2.14/1.31  %Foreground operators:
% 2.14/1.31  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.14/1.31  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.14/1.31  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.14/1.31  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.14/1.31  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.14/1.31  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.14/1.31  tff('#skF_2', type, '#skF_2': $i).
% 2.14/1.31  tff('#skF_3', type, '#skF_3': $i).
% 2.14/1.31  tff('#skF_1', type, '#skF_1': $i).
% 2.14/1.31  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.14/1.31  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.14/1.31  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.14/1.31  
% 2.14/1.32  tff(f_49, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.14/1.32  tff(f_58, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 2.14/1.32  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.14/1.32  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.14/1.32  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.14/1.32  tff(f_53, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 2.14/1.32  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.14/1.32  tff(c_20, plain, (![A_16, B_17]: (r1_tarski(k1_tarski(A_16), k2_tarski(A_16, B_17)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.14/1.32  tff(c_26, plain, (r1_tarski(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.14/1.32  tff(c_79, plain, (![A_28, B_29]: (k2_xboole_0(A_28, B_29)=B_29 | ~r1_tarski(A_28, B_29))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.14/1.32  tff(c_89, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_2'), k1_tarski('#skF_3'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_26, c_79])).
% 2.14/1.32  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.14/1.32  tff(c_147, plain, (![A_34, C_35, B_36]: (r1_tarski(A_34, k2_xboole_0(C_35, B_36)) | ~r1_tarski(A_34, B_36))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.14/1.32  tff(c_191, plain, (![A_42, A_43, B_44]: (r1_tarski(A_42, k2_xboole_0(A_43, B_44)) | ~r1_tarski(A_42, A_43))), inference(superposition, [status(thm), theory('equality')], [c_2, c_147])).
% 2.14/1.32  tff(c_243, plain, (![A_47]: (r1_tarski(A_47, k1_tarski('#skF_3')) | ~r1_tarski(A_47, k2_tarski('#skF_1', '#skF_2')))), inference(superposition, [status(thm), theory('equality')], [c_89, c_191])).
% 2.14/1.32  tff(c_252, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(resolution, [status(thm)], [c_20, c_243])).
% 2.14/1.32  tff(c_22, plain, (![B_19, A_18]: (B_19=A_18 | ~r1_tarski(k1_tarski(A_18), k1_tarski(B_19)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.14/1.32  tff(c_332, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_252, c_22])).
% 2.14/1.32  tff(c_24, plain, (k2_tarski('#skF_1', '#skF_2')!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.14/1.32  tff(c_164, plain, (![B_37, A_38]: (B_37=A_38 | ~r1_tarski(B_37, A_38) | ~r1_tarski(A_38, B_37))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.14/1.32  tff(c_168, plain, (k2_tarski('#skF_1', '#skF_2')=k1_tarski('#skF_3') | ~r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_26, c_164])).
% 2.14/1.32  tff(c_176, plain, (~r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_1', '#skF_2'))), inference(negUnitSimplification, [status(thm)], [c_24, c_168])).
% 2.14/1.32  tff(c_336, plain, (~r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_332, c_176])).
% 2.14/1.32  tff(c_343, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_20, c_336])).
% 2.14/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.14/1.32  
% 2.14/1.32  Inference rules
% 2.14/1.32  ----------------------
% 2.14/1.32  #Ref     : 0
% 2.14/1.32  #Sup     : 78
% 2.14/1.32  #Fact    : 0
% 2.14/1.32  #Define  : 0
% 2.14/1.32  #Split   : 0
% 2.14/1.32  #Chain   : 0
% 2.14/1.32  #Close   : 0
% 2.14/1.32  
% 2.14/1.32  Ordering : KBO
% 2.14/1.32  
% 2.14/1.32  Simplification rules
% 2.14/1.32  ----------------------
% 2.14/1.32  #Subsume      : 6
% 2.14/1.32  #Demod        : 26
% 2.14/1.32  #Tautology    : 45
% 2.14/1.32  #SimpNegUnit  : 1
% 2.14/1.32  #BackRed      : 7
% 2.14/1.32  
% 2.14/1.32  #Partial instantiations: 0
% 2.14/1.32  #Strategies tried      : 1
% 2.14/1.32  
% 2.14/1.32  Timing (in seconds)
% 2.14/1.32  ----------------------
% 2.14/1.32  Preprocessing        : 0.30
% 2.14/1.32  Parsing              : 0.16
% 2.14/1.32  CNF conversion       : 0.02
% 2.14/1.32  Main loop            : 0.21
% 2.14/1.32  Inferencing          : 0.07
% 2.14/1.32  Reduction            : 0.07
% 2.14/1.32  Demodulation         : 0.06
% 2.14/1.32  BG Simplification    : 0.01
% 2.14/1.32  Subsumption          : 0.04
% 2.14/1.32  Abstraction          : 0.01
% 2.14/1.32  MUC search           : 0.00
% 2.14/1.32  Cooper               : 0.00
% 2.14/1.32  Total                : 0.53
% 2.14/1.32  Index Insertion      : 0.00
% 2.14/1.33  Index Deletion       : 0.00
% 2.14/1.33  Index Matching       : 0.00
% 2.14/1.33  BG Taut test         : 0.00
%------------------------------------------------------------------------------

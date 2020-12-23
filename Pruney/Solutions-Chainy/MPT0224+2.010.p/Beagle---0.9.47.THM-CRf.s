%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:30 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   33 (  34 expanded)
%              Number of leaves         :   20 (  21 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  29 expanded)
%              Number of equality atoms :   19 (  20 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(c_20,plain,(
    ! [A_17,B_18] : r1_tarski(k1_tarski(A_17),k2_tarski(A_17,B_18)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_64,plain,(
    ! [A_29,B_30] :
      ( k4_xboole_0(A_29,B_30) = k1_xboole_0
      | ~ r1_tarski(A_29,B_30) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_72,plain,(
    ! [A_17,B_18] : k4_xboole_0(k1_tarski(A_17),k2_tarski(A_17,B_18)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_64])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_10,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_80,plain,(
    ! [A_32,B_33] :
      ( r1_tarski(A_32,B_33)
      | k4_xboole_0(A_32,B_33) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_145,plain,(
    ! [A_41,B_42] :
      ( k2_xboole_0(A_41,B_42) = B_42
      | k4_xboole_0(A_41,B_42) != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_80,c_6])).

tff(c_151,plain,(
    ! [A_7,B_8] :
      ( k2_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k3_xboole_0(A_7,B_8)
      | k4_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_145])).

tff(c_299,plain,(
    ! [A_56,B_57] :
      ( k3_xboole_0(A_56,B_57) = A_56
      | k4_xboole_0(A_56,B_57) != k1_xboole_0 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_151])).

tff(c_314,plain,(
    ! [A_17,B_18] : k3_xboole_0(k1_tarski(A_17),k2_tarski(A_17,B_18)) = k1_tarski(A_17) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_299])).

tff(c_22,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k2_tarski('#skF_1','#skF_2')) != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_370,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_314,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:10 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.26  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.26  
% 2.06/1.26  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.26  %$ r1_tarski > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.06/1.26  
% 2.06/1.26  %Foreground sorts:
% 2.06/1.26  
% 2.06/1.26  
% 2.06/1.26  %Background operators:
% 2.06/1.26  
% 2.06/1.26  
% 2.06/1.26  %Foreground operators:
% 2.06/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.26  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.06/1.26  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.06/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.06/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.26  
% 2.06/1.27  tff(f_47, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 2.06/1.27  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.06/1.27  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.06/1.27  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 2.06/1.27  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.06/1.27  tff(f_50, negated_conjecture, ~(![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 2.06/1.27  tff(c_20, plain, (![A_17, B_18]: (r1_tarski(k1_tarski(A_17), k2_tarski(A_17, B_18)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 2.06/1.27  tff(c_64, plain, (![A_29, B_30]: (k4_xboole_0(A_29, B_30)=k1_xboole_0 | ~r1_tarski(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.27  tff(c_72, plain, (![A_17, B_18]: (k4_xboole_0(k1_tarski(A_17), k2_tarski(A_17, B_18))=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_64])).
% 2.06/1.27  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.27  tff(c_10, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.06/1.27  tff(c_80, plain, (![A_32, B_33]: (r1_tarski(A_32, B_33) | k4_xboole_0(A_32, B_33)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.06/1.27  tff(c_6, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.06/1.27  tff(c_145, plain, (![A_41, B_42]: (k2_xboole_0(A_41, B_42)=B_42 | k4_xboole_0(A_41, B_42)!=k1_xboole_0)), inference(resolution, [status(thm)], [c_80, c_6])).
% 2.06/1.27  tff(c_151, plain, (![A_7, B_8]: (k2_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k3_xboole_0(A_7, B_8) | k4_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_10, c_145])).
% 2.06/1.27  tff(c_299, plain, (![A_56, B_57]: (k3_xboole_0(A_56, B_57)=A_56 | k4_xboole_0(A_56, B_57)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_151])).
% 2.06/1.27  tff(c_314, plain, (![A_17, B_18]: (k3_xboole_0(k1_tarski(A_17), k2_tarski(A_17, B_18))=k1_tarski(A_17))), inference(superposition, [status(thm), theory('equality')], [c_72, c_299])).
% 2.06/1.27  tff(c_22, plain, (k3_xboole_0(k1_tarski('#skF_1'), k2_tarski('#skF_1', '#skF_2'))!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.06/1.27  tff(c_370, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_314, c_22])).
% 2.06/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.06/1.27  
% 2.06/1.27  Inference rules
% 2.06/1.27  ----------------------
% 2.06/1.27  #Ref     : 0
% 2.06/1.27  #Sup     : 82
% 2.06/1.27  #Fact    : 0
% 2.06/1.27  #Define  : 0
% 2.06/1.27  #Split   : 0
% 2.06/1.27  #Chain   : 0
% 2.06/1.27  #Close   : 0
% 2.06/1.27  
% 2.06/1.27  Ordering : KBO
% 2.06/1.27  
% 2.06/1.27  Simplification rules
% 2.06/1.27  ----------------------
% 2.06/1.27  #Subsume      : 1
% 2.06/1.27  #Demod        : 49
% 2.06/1.27  #Tautology    : 62
% 2.06/1.27  #SimpNegUnit  : 0
% 2.06/1.27  #BackRed      : 1
% 2.06/1.27  
% 2.06/1.27  #Partial instantiations: 0
% 2.06/1.27  #Strategies tried      : 1
% 2.06/1.27  
% 2.06/1.27  Timing (in seconds)
% 2.06/1.27  ----------------------
% 2.06/1.27  Preprocessing        : 0.28
% 2.06/1.27  Parsing              : 0.15
% 2.06/1.27  CNF conversion       : 0.02
% 2.06/1.27  Main loop            : 0.19
% 2.06/1.28  Inferencing          : 0.08
% 2.06/1.28  Reduction            : 0.06
% 2.06/1.28  Demodulation         : 0.05
% 2.06/1.28  BG Simplification    : 0.01
% 2.06/1.28  Subsumption          : 0.02
% 2.06/1.28  Abstraction          : 0.01
% 2.06/1.28  MUC search           : 0.00
% 2.06/1.28  Cooper               : 0.00
% 2.06/1.28  Total                : 0.49
% 2.06/1.28  Index Insertion      : 0.00
% 2.06/1.28  Index Deletion       : 0.00
% 2.06/1.28  Index Matching       : 0.00
% 2.06/1.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------

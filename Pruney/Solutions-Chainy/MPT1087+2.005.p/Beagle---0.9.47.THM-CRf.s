%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:23 EST 2020

% Result     : Theorem 1.79s
% Output     : CNFRefutation 1.79s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    5
%              Number of atoms          :   20 (  22 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_finset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_finset_1(A)
       => v1_finset_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_finset_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,B)
        & v1_finset_1(B) )
     => v1_finset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).

tff(c_10,plain,(
    v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_18,plain,(
    ! [A_13,B_14] : k4_xboole_0(A_13,k4_xboole_0(A_13,B_14)) = k3_xboole_0(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( v1_finset_1(A_9)
      | ~ v1_finset_1(B_10)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_1,B_2] :
      ( v1_finset_1(k4_xboole_0(A_1,B_2))
      | ~ v1_finset_1(A_1) ) ),
    inference(resolution,[status(thm)],[c_2,c_12])).

tff(c_44,plain,(
    ! [A_17,B_18] :
      ( v1_finset_1(k3_xboole_0(A_17,B_18))
      | ~ v1_finset_1(A_17) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_16])).

tff(c_8,plain,(
    ~ v1_finset_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_47,plain,(
    ~ v1_finset_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_44,c_8])).

tff(c_51,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_47])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:04:52 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.79/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.24  
% 1.79/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.24  %$ r1_tarski > v1_finset_1 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.79/1.24  
% 1.79/1.24  %Foreground sorts:
% 1.79/1.24  
% 1.79/1.24  
% 1.79/1.24  %Background operators:
% 1.79/1.24  
% 1.79/1.24  
% 1.79/1.24  %Foreground operators:
% 1.79/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.79/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.79/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.79/1.24  tff('#skF_2', type, '#skF_2': $i).
% 1.79/1.24  tff('#skF_1', type, '#skF_1': $i).
% 1.79/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.79/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.79/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.79/1.24  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 1.79/1.24  
% 1.79/1.25  tff(f_40, negated_conjecture, ~(![A, B]: (v1_finset_1(A) => v1_finset_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_finset_1)).
% 1.79/1.25  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 1.79/1.25  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.79/1.25  tff(f_35, axiom, (![A, B]: ((r1_tarski(A, B) & v1_finset_1(B)) => v1_finset_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_finset_1)).
% 1.79/1.25  tff(c_10, plain, (v1_finset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.79/1.25  tff(c_18, plain, (![A_13, B_14]: (k4_xboole_0(A_13, k4_xboole_0(A_13, B_14))=k3_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.79/1.25  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.79/1.25  tff(c_12, plain, (![A_9, B_10]: (v1_finset_1(A_9) | ~v1_finset_1(B_10) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.79/1.25  tff(c_16, plain, (![A_1, B_2]: (v1_finset_1(k4_xboole_0(A_1, B_2)) | ~v1_finset_1(A_1))), inference(resolution, [status(thm)], [c_2, c_12])).
% 1.79/1.25  tff(c_44, plain, (![A_17, B_18]: (v1_finset_1(k3_xboole_0(A_17, B_18)) | ~v1_finset_1(A_17))), inference(superposition, [status(thm), theory('equality')], [c_18, c_16])).
% 1.79/1.25  tff(c_8, plain, (~v1_finset_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.79/1.25  tff(c_47, plain, (~v1_finset_1('#skF_1')), inference(resolution, [status(thm)], [c_44, c_8])).
% 1.79/1.25  tff(c_51, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_47])).
% 1.79/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.79/1.25  
% 1.79/1.25  Inference rules
% 1.79/1.25  ----------------------
% 1.79/1.25  #Ref     : 0
% 1.79/1.25  #Sup     : 9
% 1.79/1.25  #Fact    : 0
% 1.79/1.25  #Define  : 0
% 1.79/1.25  #Split   : 0
% 1.79/1.25  #Chain   : 0
% 1.79/1.25  #Close   : 0
% 1.79/1.25  
% 1.79/1.25  Ordering : KBO
% 1.79/1.25  
% 1.79/1.25  Simplification rules
% 1.79/1.25  ----------------------
% 1.79/1.25  #Subsume      : 0
% 1.79/1.25  #Demod        : 1
% 1.79/1.25  #Tautology    : 2
% 1.79/1.25  #SimpNegUnit  : 0
% 1.79/1.25  #BackRed      : 0
% 1.79/1.25  
% 1.79/1.25  #Partial instantiations: 0
% 1.79/1.25  #Strategies tried      : 1
% 1.79/1.25  
% 1.79/1.25  Timing (in seconds)
% 1.79/1.25  ----------------------
% 1.79/1.25  Preprocessing        : 0.28
% 1.79/1.25  Parsing              : 0.15
% 1.79/1.25  CNF conversion       : 0.02
% 1.79/1.25  Main loop            : 0.10
% 1.79/1.25  Inferencing          : 0.05
% 1.79/1.25  Reduction            : 0.02
% 1.79/1.25  Demodulation         : 0.02
% 1.79/1.25  BG Simplification    : 0.01
% 1.79/1.25  Subsumption          : 0.01
% 1.79/1.25  Abstraction          : 0.00
% 1.79/1.25  MUC search           : 0.00
% 1.79/1.25  Cooper               : 0.00
% 1.79/1.25  Total                : 0.40
% 1.79/1.25  Index Insertion      : 0.00
% 1.79/1.25  Index Deletion       : 0.00
% 1.79/1.25  Index Matching       : 0.00
% 1.79/1.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------

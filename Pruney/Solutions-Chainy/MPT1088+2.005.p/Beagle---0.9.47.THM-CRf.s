%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:24 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   19 (  21 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_finset_1 > k6_subset_1 > k4_xboole_0 > #nlpp > #skF_2 > #skF_1

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

tff(k6_subset_1,type,(
    k6_subset_1: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_finset_1(A)
       => v1_finset_1(k6_subset_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_finset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,B)
        & v1_finset_1(B) )
     => v1_finset_1(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_finset_1)).

tff(f_29,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_10,plain,(
    v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k4_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_22,plain,(
    ! [A_11,B_12] :
      ( v1_finset_1(A_11)
      | ~ v1_finset_1(B_12)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_27,plain,(
    ! [A_13,B_14] :
      ( v1_finset_1(k4_xboole_0(A_13,B_14))
      | ~ v1_finset_1(A_13) ) ),
    inference(resolution,[status(thm)],[c_2,c_22])).

tff(c_4,plain,(
    ! [A_3,B_4] : k6_subset_1(A_3,B_4) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_8,plain,(
    ~ v1_finset_1(k6_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_11,plain,(
    ~ v1_finset_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_8])).

tff(c_30,plain,(
    ~ v1_finset_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_27,c_11])).

tff(c_34,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_30])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:03:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.05  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.06  
% 1.51/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.06  %$ r1_tarski > v1_finset_1 > k6_subset_1 > k4_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.51/1.06  
% 1.51/1.06  %Foreground sorts:
% 1.51/1.06  
% 1.51/1.06  
% 1.51/1.06  %Background operators:
% 1.51/1.06  
% 1.51/1.06  
% 1.51/1.06  %Foreground operators:
% 1.51/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.51/1.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.51/1.06  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.51/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.51/1.06  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.51/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.51/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.51/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.51/1.06  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 1.51/1.06  
% 1.51/1.07  tff(f_40, negated_conjecture, ~(![A, B]: (v1_finset_1(A) => v1_finset_1(k6_subset_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_finset_1)).
% 1.51/1.07  tff(f_27, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t36_xboole_1)).
% 1.51/1.07  tff(f_35, axiom, (![A, B]: ((r1_tarski(A, B) & v1_finset_1(B)) => v1_finset_1(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_finset_1)).
% 1.51/1.07  tff(f_29, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.51/1.07  tff(c_10, plain, (v1_finset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.51/1.07  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k4_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.51/1.07  tff(c_22, plain, (![A_11, B_12]: (v1_finset_1(A_11) | ~v1_finset_1(B_12) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.51/1.07  tff(c_27, plain, (![A_13, B_14]: (v1_finset_1(k4_xboole_0(A_13, B_14)) | ~v1_finset_1(A_13))), inference(resolution, [status(thm)], [c_2, c_22])).
% 1.51/1.07  tff(c_4, plain, (![A_3, B_4]: (k6_subset_1(A_3, B_4)=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.51/1.07  tff(c_8, plain, (~v1_finset_1(k6_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.51/1.07  tff(c_11, plain, (~v1_finset_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_8])).
% 1.51/1.07  tff(c_30, plain, (~v1_finset_1('#skF_1')), inference(resolution, [status(thm)], [c_27, c_11])).
% 1.51/1.07  tff(c_34, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_30])).
% 1.51/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.07  
% 1.51/1.07  Inference rules
% 1.51/1.07  ----------------------
% 1.51/1.07  #Ref     : 0
% 1.51/1.07  #Sup     : 4
% 1.51/1.07  #Fact    : 0
% 1.51/1.07  #Define  : 0
% 1.51/1.07  #Split   : 0
% 1.51/1.07  #Chain   : 0
% 1.51/1.07  #Close   : 0
% 1.51/1.07  
% 1.51/1.07  Ordering : KBO
% 1.51/1.07  
% 1.51/1.07  Simplification rules
% 1.51/1.07  ----------------------
% 1.51/1.07  #Subsume      : 0
% 1.51/1.07  #Demod        : 2
% 1.51/1.07  #Tautology    : 2
% 1.51/1.07  #SimpNegUnit  : 0
% 1.51/1.07  #BackRed      : 0
% 1.51/1.07  
% 1.51/1.07  #Partial instantiations: 0
% 1.51/1.07  #Strategies tried      : 1
% 1.51/1.07  
% 1.51/1.07  Timing (in seconds)
% 1.51/1.07  ----------------------
% 1.51/1.07  Preprocessing        : 0.26
% 1.51/1.07  Parsing              : 0.14
% 1.51/1.07  CNF conversion       : 0.01
% 1.51/1.07  Main loop            : 0.06
% 1.51/1.07  Inferencing          : 0.03
% 1.51/1.07  Reduction            : 0.02
% 1.51/1.07  Demodulation         : 0.01
% 1.51/1.07  BG Simplification    : 0.01
% 1.51/1.07  Subsumption          : 0.00
% 1.51/1.07  Abstraction          : 0.01
% 1.51/1.07  MUC search           : 0.00
% 1.51/1.07  Cooper               : 0.00
% 1.51/1.07  Total                : 0.34
% 1.51/1.07  Index Insertion      : 0.00
% 1.51/1.07  Index Deletion       : 0.00
% 1.51/1.07  Index Matching       : 0.00
% 1.51/1.07  BG Taut test         : 0.00
%------------------------------------------------------------------------------

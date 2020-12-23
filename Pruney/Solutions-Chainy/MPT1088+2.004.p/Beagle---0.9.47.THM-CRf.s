%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:24 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.65s
% Verified   : 
% Statistics : Number of formulae       :   18 (  19 expanded)
%              Number of leaves         :   11 (  12 expanded)
%              Depth                    :    4
%              Number of atoms          :   13 (  15 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_finset_1 > k6_subset_1 > k4_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_36,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_finset_1(A)
       => v1_finset_1(k6_subset_1(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_finset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( v1_finset_1(A)
     => v1_finset_1(k4_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc12_finset_1)).

tff(f_27,axiom,(
    ! [A,B] : k6_subset_1(A,B) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',redefinition_k6_subset_1)).

tff(c_8,plain,(
    v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_19,plain,(
    ! [A_7,B_8] :
      ( v1_finset_1(k4_xboole_0(A_7,B_8))
      | ~ v1_finset_1(A_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_2,plain,(
    ! [A_1,B_2] : k6_subset_1(A_1,B_2) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_6,plain,(
    ~ v1_finset_1(k6_subset_1('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_9,plain,(
    ~ v1_finset_1(k4_xboole_0('#skF_1','#skF_2')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_6])).

tff(c_22,plain,(
    ~ v1_finset_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_19,c_9])).

tff(c_26,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_22])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:19:34 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.16  
% 1.51/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.51/1.17  %$ v1_finset_1 > k6_subset_1 > k4_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.51/1.17  
% 1.51/1.17  %Foreground sorts:
% 1.51/1.17  
% 1.51/1.17  
% 1.51/1.17  %Background operators:
% 1.51/1.17  
% 1.51/1.17  
% 1.51/1.17  %Foreground operators:
% 1.51/1.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.51/1.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.51/1.17  tff('#skF_2', type, '#skF_2': $i).
% 1.51/1.17  tff(k6_subset_1, type, k6_subset_1: ($i * $i) > $i).
% 1.51/1.17  tff('#skF_1', type, '#skF_1': $i).
% 1.51/1.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.51/1.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.51/1.17  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 1.51/1.17  
% 1.65/1.17  tff(f_36, negated_conjecture, ~(![A, B]: (v1_finset_1(A) => v1_finset_1(k6_subset_1(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_finset_1)).
% 1.65/1.17  tff(f_31, axiom, (![A, B]: (v1_finset_1(A) => v1_finset_1(k4_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc12_finset_1)).
% 1.65/1.17  tff(f_27, axiom, (![A, B]: (k6_subset_1(A, B) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', redefinition_k6_subset_1)).
% 1.65/1.17  tff(c_8, plain, (v1_finset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.65/1.17  tff(c_19, plain, (![A_7, B_8]: (v1_finset_1(k4_xboole_0(A_7, B_8)) | ~v1_finset_1(A_7))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.65/1.17  tff(c_2, plain, (![A_1, B_2]: (k6_subset_1(A_1, B_2)=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.65/1.17  tff(c_6, plain, (~v1_finset_1(k6_subset_1('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.65/1.17  tff(c_9, plain, (~v1_finset_1(k4_xboole_0('#skF_1', '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_6])).
% 1.65/1.17  tff(c_22, plain, (~v1_finset_1('#skF_1')), inference(resolution, [status(thm)], [c_19, c_9])).
% 1.65/1.17  tff(c_26, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_22])).
% 1.65/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.65/1.17  
% 1.65/1.17  Inference rules
% 1.65/1.17  ----------------------
% 1.65/1.17  #Ref     : 0
% 1.65/1.17  #Sup     : 3
% 1.65/1.17  #Fact    : 0
% 1.65/1.17  #Define  : 0
% 1.65/1.17  #Split   : 0
% 1.65/1.17  #Chain   : 0
% 1.65/1.17  #Close   : 0
% 1.65/1.17  
% 1.65/1.17  Ordering : KBO
% 1.65/1.17  
% 1.65/1.17  Simplification rules
% 1.65/1.17  ----------------------
% 1.65/1.17  #Subsume      : 0
% 1.65/1.17  #Demod        : 2
% 1.65/1.17  #Tautology    : 2
% 1.65/1.17  #SimpNegUnit  : 0
% 1.65/1.17  #BackRed      : 0
% 1.65/1.17  
% 1.65/1.17  #Partial instantiations: 0
% 1.65/1.17  #Strategies tried      : 1
% 1.65/1.17  
% 1.65/1.17  Timing (in seconds)
% 1.65/1.17  ----------------------
% 1.65/1.18  Preprocessing        : 0.30
% 1.65/1.18  Parsing              : 0.16
% 1.65/1.18  CNF conversion       : 0.02
% 1.65/1.18  Main loop            : 0.07
% 1.65/1.18  Inferencing          : 0.03
% 1.65/1.18  Reduction            : 0.02
% 1.65/1.18  Demodulation         : 0.02
% 1.65/1.18  BG Simplification    : 0.01
% 1.65/1.18  Subsumption          : 0.01
% 1.65/1.18  Abstraction          : 0.01
% 1.65/1.18  MUC search           : 0.00
% 1.65/1.18  Cooper               : 0.00
% 1.65/1.18  Total                : 0.39
% 1.65/1.18  Index Insertion      : 0.00
% 1.65/1.18  Index Deletion       : 0.00
% 1.65/1.18  Index Matching       : 0.00
% 1.65/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

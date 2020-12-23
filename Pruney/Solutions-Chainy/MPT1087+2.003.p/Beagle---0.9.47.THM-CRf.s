%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:23 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   20 (  21 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   16 (  18 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > v1_finset_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_40,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_finset_1(A)
       => v1_finset_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_finset_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( ( r1_tarski(A,B)
        & v1_finset_1(B) )
     => v1_finset_1(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t13_finset_1)).

tff(c_10,plain,(
    v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_tarski(k3_xboole_0(A_1,B_2),A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( v1_finset_1(A_9)
      | ~ v1_finset_1(B_10)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_17,plain,(
    ! [A_11,B_12] :
      ( v1_finset_1(k3_xboole_0(A_11,B_12))
      | ~ v1_finset_1(A_11) ) ),
    inference(resolution,[status(thm)],[c_2,c_12])).

tff(c_8,plain,(
    ~ v1_finset_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_20,plain,(
    ~ v1_finset_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_17,c_8])).

tff(c_24,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_20])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n024.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:06:21 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.10  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.10  
% 1.54/1.10  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.10  %$ r1_tarski > v1_finset_1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > #skF_2 > #skF_1
% 1.54/1.10  
% 1.54/1.10  %Foreground sorts:
% 1.54/1.10  
% 1.54/1.10  
% 1.54/1.10  %Background operators:
% 1.54/1.10  
% 1.54/1.10  
% 1.54/1.10  %Foreground operators:
% 1.54/1.10  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.54/1.10  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.54/1.10  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.54/1.10  tff('#skF_2', type, '#skF_2': $i).
% 1.54/1.10  tff('#skF_1', type, '#skF_1': $i).
% 1.54/1.10  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.54/1.10  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.54/1.10  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.54/1.10  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 1.54/1.10  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 1.54/1.10  
% 1.54/1.11  tff(f_40, negated_conjecture, ~(![A, B]: (v1_finset_1(A) => v1_finset_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_finset_1)).
% 1.54/1.11  tff(f_27, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 1.54/1.11  tff(f_35, axiom, (![A, B]: ((r1_tarski(A, B) & v1_finset_1(B)) => v1_finset_1(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t13_finset_1)).
% 1.54/1.11  tff(c_10, plain, (v1_finset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.54/1.11  tff(c_2, plain, (![A_1, B_2]: (r1_tarski(k3_xboole_0(A_1, B_2), A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.54/1.11  tff(c_12, plain, (![A_9, B_10]: (v1_finset_1(A_9) | ~v1_finset_1(B_10) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.54/1.11  tff(c_17, plain, (![A_11, B_12]: (v1_finset_1(k3_xboole_0(A_11, B_12)) | ~v1_finset_1(A_11))), inference(resolution, [status(thm)], [c_2, c_12])).
% 1.54/1.11  tff(c_8, plain, (~v1_finset_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.54/1.11  tff(c_20, plain, (~v1_finset_1('#skF_1')), inference(resolution, [status(thm)], [c_17, c_8])).
% 1.54/1.11  tff(c_24, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_10, c_20])).
% 1.54/1.11  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.11  
% 1.54/1.11  Inference rules
% 1.54/1.11  ----------------------
% 1.54/1.11  #Ref     : 0
% 1.54/1.11  #Sup     : 2
% 1.54/1.11  #Fact    : 0
% 1.54/1.11  #Define  : 0
% 1.54/1.11  #Split   : 0
% 1.54/1.11  #Chain   : 0
% 1.54/1.11  #Close   : 0
% 1.54/1.11  
% 1.54/1.11  Ordering : KBO
% 1.54/1.11  
% 1.54/1.11  Simplification rules
% 1.54/1.11  ----------------------
% 1.54/1.11  #Subsume      : 0
% 1.54/1.11  #Demod        : 1
% 1.54/1.11  #Tautology    : 0
% 1.54/1.11  #SimpNegUnit  : 0
% 1.54/1.11  #BackRed      : 0
% 1.54/1.11  
% 1.54/1.11  #Partial instantiations: 0
% 1.54/1.11  #Strategies tried      : 1
% 1.54/1.11  
% 1.54/1.11  Timing (in seconds)
% 1.54/1.11  ----------------------
% 1.54/1.11  Preprocessing        : 0.25
% 1.54/1.11  Parsing              : 0.15
% 1.54/1.11  CNF conversion       : 0.01
% 1.54/1.11  Main loop            : 0.07
% 1.54/1.11  Inferencing          : 0.04
% 1.54/1.11  Reduction            : 0.02
% 1.54/1.11  Demodulation         : 0.01
% 1.54/1.11  BG Simplification    : 0.01
% 1.54/1.11  Subsumption          : 0.00
% 1.54/1.11  Abstraction          : 0.00
% 1.54/1.11  MUC search           : 0.00
% 1.54/1.11  Cooper               : 0.00
% 1.54/1.11  Total                : 0.34
% 1.54/1.11  Index Insertion      : 0.00
% 1.54/1.11  Index Deletion       : 0.00
% 1.54/1.11  Index Matching       : 0.00
% 1.54/1.11  BG Taut test         : 0.00
%------------------------------------------------------------------------------

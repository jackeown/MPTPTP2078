%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:23 EST 2020

% Result     : Theorem 1.40s
% Output     : CNFRefutation 1.50s
% Verified   : 
% Statistics : Number of formulae       :   14 (  15 expanded)
%              Number of leaves         :    9 (  10 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  12 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_finset_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_34,negated_conjecture,(
    ~ ! [A,B] :
        ( v1_finset_1(A)
       => v1_finset_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_finset_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( v1_finset_1(A)
     => v1_finset_1(k3_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc11_finset_1)).

tff(c_6,plain,(
    v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_7,plain,(
    ! [A_3,B_4] :
      ( v1_finset_1(k3_xboole_0(A_3,B_4))
      | ~ v1_finset_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_4,plain,(
    ~ v1_finset_1(k3_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_10,plain,(
    ~ v1_finset_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_7,c_4])).

tff(c_14,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_10])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n005.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:41:47 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.40/1.00  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.40/1.00  
% 1.40/1.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.40/1.01  %$ v1_finset_1 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.40/1.01  
% 1.40/1.01  %Foreground sorts:
% 1.40/1.01  
% 1.40/1.01  
% 1.40/1.01  %Background operators:
% 1.40/1.01  
% 1.40/1.01  
% 1.40/1.01  %Foreground operators:
% 1.40/1.01  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.40/1.01  tff('#skF_2', type, '#skF_2': $i).
% 1.40/1.01  tff('#skF_1', type, '#skF_1': $i).
% 1.40/1.01  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.40/1.01  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.40/1.01  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.40/1.01  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 1.40/1.01  
% 1.50/1.02  tff(f_34, negated_conjecture, ~(![A, B]: (v1_finset_1(A) => v1_finset_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_finset_1)).
% 1.50/1.02  tff(f_29, axiom, (![A, B]: (v1_finset_1(A) => v1_finset_1(k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc11_finset_1)).
% 1.50/1.02  tff(c_6, plain, (v1_finset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.50/1.02  tff(c_7, plain, (![A_3, B_4]: (v1_finset_1(k3_xboole_0(A_3, B_4)) | ~v1_finset_1(A_3))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.50/1.02  tff(c_4, plain, (~v1_finset_1(k3_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.50/1.02  tff(c_10, plain, (~v1_finset_1('#skF_1')), inference(resolution, [status(thm)], [c_7, c_4])).
% 1.50/1.02  tff(c_14, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_10])).
% 1.50/1.02  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.50/1.02  
% 1.50/1.02  Inference rules
% 1.50/1.02  ----------------------
% 1.50/1.02  #Ref     : 0
% 1.50/1.02  #Sup     : 1
% 1.50/1.02  #Fact    : 0
% 1.50/1.02  #Define  : 0
% 1.50/1.02  #Split   : 0
% 1.50/1.02  #Chain   : 0
% 1.50/1.02  #Close   : 0
% 1.50/1.02  
% 1.50/1.02  Ordering : KBO
% 1.50/1.02  
% 1.50/1.02  Simplification rules
% 1.50/1.02  ----------------------
% 1.50/1.02  #Subsume      : 0
% 1.50/1.02  #Demod        : 1
% 1.50/1.02  #Tautology    : 0
% 1.50/1.02  #SimpNegUnit  : 0
% 1.50/1.02  #BackRed      : 0
% 1.50/1.02  
% 1.50/1.02  #Partial instantiations: 0
% 1.50/1.02  #Strategies tried      : 1
% 1.50/1.02  
% 1.50/1.02  Timing (in seconds)
% 1.50/1.02  ----------------------
% 1.50/1.02  Preprocessing        : 0.23
% 1.50/1.02  Parsing              : 0.12
% 1.50/1.02  CNF conversion       : 0.01
% 1.50/1.02  Main loop            : 0.05
% 1.50/1.02  Inferencing          : 0.02
% 1.50/1.02  Reduction            : 0.01
% 1.50/1.02  Demodulation         : 0.01
% 1.50/1.02  BG Simplification    : 0.01
% 1.50/1.02  Subsumption          : 0.00
% 1.50/1.02  Abstraction          : 0.00
% 1.50/1.02  MUC search           : 0.00
% 1.50/1.02  Cooper               : 0.00
% 1.50/1.02  Total                : 0.30
% 1.50/1.02  Index Insertion      : 0.00
% 1.50/1.02  Index Deletion       : 0.00
% 1.50/1.02  Index Matching       : 0.00
% 1.50/1.03  BG Taut test         : 0.00
%------------------------------------------------------------------------------

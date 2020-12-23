%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 10:18:23 EST 2020

% Result     : Theorem 1.68s
% Output     : CNFRefutation 1.70s
% Verified   : 
% Statistics : Number of formulae       :   15 (  17 expanded)
%              Number of leaves         :    9 (  11 expanded)
%              Depth                    :    3
%              Number of atoms          :   15 (  21 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ v1_finset_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_finset_1,type,(
    v1_finset_1: $i > $o )).

tff(f_38,negated_conjecture,(
    ~ ! [A,B] :
        ( ( v1_finset_1(A)
          & v1_finset_1(B) )
       => v1_finset_1(k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t14_finset_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( ( v1_finset_1(A)
        & v1_finset_1(B) )
     => v1_finset_1(k2_xboole_0(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc9_finset_1)).

tff(c_8,plain,(
    v1_finset_1('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_6,plain,(
    v1_finset_1('#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_9,plain,(
    ! [A_3,B_4] :
      ( v1_finset_1(k2_xboole_0(A_3,B_4))
      | ~ v1_finset_1(B_4)
      | ~ v1_finset_1(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ~ v1_finset_1(k2_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_12,plain,
    ( ~ v1_finset_1('#skF_2')
    | ~ v1_finset_1('#skF_1') ),
    inference(resolution,[status(thm)],[c_9,c_4])).

tff(c_16,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_6,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:29:56 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.68/1.23  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.68/1.24  
% 1.68/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.25  %$ v1_finset_1 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.70/1.25  
% 1.70/1.25  %Foreground sorts:
% 1.70/1.25  
% 1.70/1.25  
% 1.70/1.25  %Background operators:
% 1.70/1.25  
% 1.70/1.25  
% 1.70/1.25  %Foreground operators:
% 1.70/1.25  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.70/1.25  tff('#skF_2', type, '#skF_2': $i).
% 1.70/1.25  tff('#skF_1', type, '#skF_1': $i).
% 1.70/1.25  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.70/1.25  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.70/1.25  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.70/1.25  tff(v1_finset_1, type, v1_finset_1: $i > $o).
% 1.70/1.25  
% 1.70/1.25  tff(f_38, negated_conjecture, ~(![A, B]: ((v1_finset_1(A) & v1_finset_1(B)) => v1_finset_1(k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t14_finset_1)).
% 1.70/1.25  tff(f_31, axiom, (![A, B]: ((v1_finset_1(A) & v1_finset_1(B)) => v1_finset_1(k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc9_finset_1)).
% 1.70/1.25  tff(c_8, plain, (v1_finset_1('#skF_1')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.70/1.25  tff(c_6, plain, (v1_finset_1('#skF_2')), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.70/1.25  tff(c_9, plain, (![A_3, B_4]: (v1_finset_1(k2_xboole_0(A_3, B_4)) | ~v1_finset_1(B_4) | ~v1_finset_1(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.70/1.25  tff(c_4, plain, (~v1_finset_1(k2_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.70/1.25  tff(c_12, plain, (~v1_finset_1('#skF_2') | ~v1_finset_1('#skF_1')), inference(resolution, [status(thm)], [c_9, c_4])).
% 1.70/1.25  tff(c_16, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_6, c_12])).
% 1.70/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.70/1.25  
% 1.70/1.25  Inference rules
% 1.70/1.25  ----------------------
% 1.70/1.25  #Ref     : 0
% 1.70/1.25  #Sup     : 1
% 1.70/1.25  #Fact    : 0
% 1.70/1.25  #Define  : 0
% 1.70/1.25  #Split   : 0
% 1.70/1.25  #Chain   : 0
% 1.70/1.25  #Close   : 0
% 1.70/1.25  
% 1.70/1.25  Ordering : KBO
% 1.70/1.25  
% 1.70/1.25  Simplification rules
% 1.70/1.25  ----------------------
% 1.70/1.25  #Subsume      : 0
% 1.70/1.25  #Demod        : 2
% 1.70/1.25  #Tautology    : 0
% 1.70/1.25  #SimpNegUnit  : 0
% 1.70/1.25  #BackRed      : 0
% 1.70/1.25  
% 1.70/1.25  #Partial instantiations: 0
% 1.70/1.25  #Strategies tried      : 1
% 1.70/1.25  
% 1.70/1.25  Timing (in seconds)
% 1.70/1.25  ----------------------
% 1.70/1.25  Preprocessing        : 0.35
% 1.70/1.26  Parsing              : 0.21
% 1.70/1.26  CNF conversion       : 0.02
% 1.70/1.26  Main loop            : 0.05
% 1.70/1.26  Inferencing          : 0.02
% 1.70/1.26  Reduction            : 0.01
% 1.70/1.26  Demodulation         : 0.01
% 1.70/1.26  BG Simplification    : 0.01
% 1.70/1.26  Subsumption          : 0.00
% 1.70/1.26  Abstraction          : 0.00
% 1.70/1.26  MUC search           : 0.00
% 1.70/1.26  Cooper               : 0.00
% 1.70/1.26  Total                : 0.43
% 1.70/1.26  Index Insertion      : 0.00
% 1.70/1.26  Index Deletion       : 0.00
% 1.70/1.26  Index Matching       : 0.00
% 1.70/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------

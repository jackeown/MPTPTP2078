%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:24 EST 2020

% Result     : Theorem 1.54s
% Output     : CNFRefutation 1.54s
% Verified   : 
% Statistics : Number of formulae       :   16 (  16 expanded)
%              Number of leaves         :   11 (  11 expanded)
%              Depth                    :    3
%              Number of atoms          :   10 (  10 expanded)
%              Number of equality atoms :    5 (   5 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_36,negated_conjecture,(
    ~ ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(c_6,plain,(
    ! [A_3] : k3_xboole_0(A_3,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_18,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(A_7,B_8)
      | k3_xboole_0(A_7,B_8) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ~ r1_xboole_0('#skF_1',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_21,plain,(
    k3_xboole_0('#skF_1',k1_xboole_0) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_10])).

tff(c_25,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_21])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 17:05:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.54/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.12  
% 1.54/1.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.12  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > k1_xboole_0 > #skF_1
% 1.54/1.12  
% 1.54/1.12  %Foreground sorts:
% 1.54/1.12  
% 1.54/1.12  
% 1.54/1.12  %Background operators:
% 1.54/1.12  
% 1.54/1.12  
% 1.54/1.12  %Foreground operators:
% 1.54/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.54/1.12  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.54/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.54/1.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.54/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.54/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.54/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.54/1.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.54/1.12  
% 1.54/1.13  tff(f_31, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 1.54/1.13  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.54/1.13  tff(f_36, negated_conjecture, ~(![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.54/1.13  tff(c_6, plain, (![A_3]: (k3_xboole_0(A_3, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.54/1.13  tff(c_18, plain, (![A_7, B_8]: (r1_xboole_0(A_7, B_8) | k3_xboole_0(A_7, B_8)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.54/1.13  tff(c_10, plain, (~r1_xboole_0('#skF_1', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.54/1.13  tff(c_21, plain, (k3_xboole_0('#skF_1', k1_xboole_0)!=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_10])).
% 1.54/1.13  tff(c_25, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_21])).
% 1.54/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.54/1.13  
% 1.54/1.13  Inference rules
% 1.54/1.13  ----------------------
% 1.54/1.13  #Ref     : 0
% 1.54/1.13  #Sup     : 3
% 1.54/1.13  #Fact    : 0
% 1.54/1.13  #Define  : 0
% 1.54/1.13  #Split   : 0
% 1.54/1.13  #Chain   : 0
% 1.54/1.13  #Close   : 0
% 1.54/1.13  
% 1.54/1.13  Ordering : KBO
% 1.54/1.13  
% 1.54/1.13  Simplification rules
% 1.54/1.13  ----------------------
% 1.54/1.13  #Subsume      : 0
% 1.54/1.13  #Demod        : 1
% 1.54/1.13  #Tautology    : 2
% 1.54/1.13  #SimpNegUnit  : 0
% 1.54/1.13  #BackRed      : 0
% 1.54/1.13  
% 1.54/1.13  #Partial instantiations: 0
% 1.54/1.13  #Strategies tried      : 1
% 1.54/1.13  
% 1.54/1.13  Timing (in seconds)
% 1.54/1.13  ----------------------
% 1.54/1.13  Preprocessing        : 0.26
% 1.54/1.13  Parsing              : 0.14
% 1.54/1.13  CNF conversion       : 0.02
% 1.54/1.13  Main loop            : 0.07
% 1.54/1.13  Inferencing          : 0.03
% 1.54/1.13  Reduction            : 0.02
% 1.54/1.13  Demodulation         : 0.01
% 1.54/1.13  BG Simplification    : 0.01
% 1.54/1.13  Subsumption          : 0.01
% 1.54/1.13  Abstraction          : 0.00
% 1.54/1.13  MUC search           : 0.00
% 1.54/1.13  Cooper               : 0.00
% 1.54/1.13  Total                : 0.35
% 1.54/1.13  Index Insertion      : 0.00
% 1.54/1.13  Index Deletion       : 0.00
% 1.54/1.13  Index Matching       : 0.00
% 1.54/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------

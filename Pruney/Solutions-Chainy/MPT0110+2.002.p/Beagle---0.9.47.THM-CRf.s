%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:45:07 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.89s
% Verified   : 
% Statistics : Number of formulae       :   21 (  21 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   13 (  13 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_33,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k4_xboole_0(k2_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l98_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_44,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t103_xboole_1)).

tff(c_155,plain,(
    ! [A_33,B_34] : k4_xboole_0(k2_xboole_0(A_33,B_34),k3_xboole_0(A_33,B_34)) = k5_xboole_0(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_12,B_13] : r1_xboole_0(k4_xboole_0(A_12,B_13),B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_51,plain,(
    ! [B_20,A_21] :
      ( r1_xboole_0(B_20,A_21)
      | ~ r1_xboole_0(A_21,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_54,plain,(
    ! [B_13,A_12] : r1_xboole_0(B_13,k4_xboole_0(A_12,B_13)) ),
    inference(resolution,[status(thm)],[c_12,c_51])).

tff(c_164,plain,(
    ! [A_33,B_34] : r1_xboole_0(k3_xboole_0(A_33,B_34),k5_xboole_0(A_33,B_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_155,c_54])).

tff(c_16,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_206,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_164,c_16])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n007.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 12:58:06 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.18  
% 1.64/1.18  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.18  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.64/1.18  
% 1.64/1.18  %Foreground sorts:
% 1.64/1.18  
% 1.64/1.18  
% 1.64/1.18  %Background operators:
% 1.64/1.18  
% 1.64/1.18  
% 1.64/1.18  %Foreground operators:
% 1.64/1.18  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.18  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.64/1.18  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.64/1.18  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.64/1.18  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.18  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.18  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.18  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.18  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.64/1.18  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.64/1.18  
% 1.89/1.19  tff(f_33, axiom, (![A, B]: (k5_xboole_0(A, B) = k4_xboole_0(k2_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l98_xboole_1)).
% 1.89/1.19  tff(f_39, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.89/1.19  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 1.89/1.19  tff(f_44, negated_conjecture, ~(![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t103_xboole_1)).
% 1.89/1.19  tff(c_155, plain, (![A_33, B_34]: (k4_xboole_0(k2_xboole_0(A_33, B_34), k3_xboole_0(A_33, B_34))=k5_xboole_0(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.89/1.19  tff(c_12, plain, (![A_12, B_13]: (r1_xboole_0(k4_xboole_0(A_12, B_13), B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 1.89/1.19  tff(c_51, plain, (![B_20, A_21]: (r1_xboole_0(B_20, A_21) | ~r1_xboole_0(A_21, B_20))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.89/1.19  tff(c_54, plain, (![B_13, A_12]: (r1_xboole_0(B_13, k4_xboole_0(A_12, B_13)))), inference(resolution, [status(thm)], [c_12, c_51])).
% 1.89/1.19  tff(c_164, plain, (![A_33, B_34]: (r1_xboole_0(k3_xboole_0(A_33, B_34), k5_xboole_0(A_33, B_34)))), inference(superposition, [status(thm), theory('equality')], [c_155, c_54])).
% 1.89/1.19  tff(c_16, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.89/1.19  tff(c_206, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_164, c_16])).
% 1.89/1.19  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.89/1.19  
% 1.89/1.19  Inference rules
% 1.89/1.19  ----------------------
% 1.89/1.19  #Ref     : 0
% 1.89/1.19  #Sup     : 49
% 1.89/1.19  #Fact    : 0
% 1.89/1.19  #Define  : 0
% 1.89/1.19  #Split   : 0
% 1.89/1.19  #Chain   : 0
% 1.89/1.19  #Close   : 0
% 1.89/1.19  
% 1.89/1.19  Ordering : KBO
% 1.89/1.19  
% 1.89/1.19  Simplification rules
% 1.89/1.19  ----------------------
% 1.89/1.19  #Subsume      : 0
% 1.89/1.19  #Demod        : 11
% 1.89/1.19  #Tautology    : 26
% 1.89/1.19  #SimpNegUnit  : 0
% 1.89/1.19  #BackRed      : 1
% 1.89/1.19  
% 1.89/1.19  #Partial instantiations: 0
% 1.89/1.19  #Strategies tried      : 1
% 1.89/1.19  
% 1.89/1.19  Timing (in seconds)
% 1.89/1.19  ----------------------
% 1.89/1.19  Preprocessing        : 0.27
% 1.89/1.19  Parsing              : 0.15
% 1.89/1.19  CNF conversion       : 0.02
% 1.89/1.19  Main loop            : 0.15
% 1.89/1.19  Inferencing          : 0.05
% 1.89/1.19  Reduction            : 0.06
% 1.89/1.19  Demodulation         : 0.05
% 1.89/1.19  BG Simplification    : 0.01
% 1.89/1.19  Subsumption          : 0.02
% 1.89/1.19  Abstraction          : 0.01
% 1.89/1.19  MUC search           : 0.00
% 1.89/1.19  Cooper               : 0.00
% 1.89/1.19  Total                : 0.44
% 1.89/1.19  Index Insertion      : 0.00
% 1.89/1.19  Index Deletion       : 0.00
% 1.89/1.19  Index Matching       : 0.00
% 1.89/1.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

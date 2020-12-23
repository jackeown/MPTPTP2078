%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:35 EST 2020

% Result     : Theorem 1.67s
% Output     : CNFRefutation 1.67s
% Verified   : 
% Statistics : Number of formulae       :   25 (  25 expanded)
%              Number of leaves         :   14 (  14 expanded)
%              Depth                    :    6
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :    0 (   0 expanded)
%              Maximal formula depth    :    6 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_37,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(k3_xboole_0(C,A),k3_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t76_xboole_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ~ ( ~ r1_xboole_0(A,B)
        & r1_xboole_0(k3_xboole_0(A,B),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t75_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,k4_xboole_0(B,C))
     => r1_xboole_0(B,k4_xboole_0(A,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t81_xboole_1)).

tff(f_48,negated_conjecture,(
    ~ ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t89_xboole_1)).

tff(c_6,plain,(
    ! [A_6,B_7] : r1_xboole_0(k4_xboole_0(A_6,B_7),B_7) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_4,plain,(
    ! [C_5,A_3,B_4] :
      ( r1_xboole_0(k3_xboole_0(C_5,A_3),k3_xboole_0(C_5,B_4))
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_15,plain,(
    ! [A_18,B_19,C_20] :
      ( r1_xboole_0(A_18,k4_xboole_0(B_19,C_20))
      | ~ r1_xboole_0(A_18,B_19) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( ~ r1_xboole_0(k3_xboole_0(A_1,B_2),B_2)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_70,plain,(
    ! [A_35,B_36,C_37] :
      ( r1_xboole_0(A_35,k4_xboole_0(B_36,C_37))
      | ~ r1_xboole_0(k3_xboole_0(A_35,k4_xboole_0(B_36,C_37)),B_36) ) ),
    inference(resolution,[status(thm)],[c_15,c_2])).

tff(c_123,plain,(
    ! [C_49,B_50,C_51] :
      ( r1_xboole_0(C_49,k4_xboole_0(k3_xboole_0(C_49,B_50),C_51))
      | ~ r1_xboole_0(k4_xboole_0(k3_xboole_0(C_49,B_50),C_51),B_50) ) ),
    inference(resolution,[status(thm)],[c_4,c_70])).

tff(c_136,plain,(
    ! [C_52,B_53] : r1_xboole_0(C_52,k4_xboole_0(k3_xboole_0(C_52,B_53),B_53)) ),
    inference(resolution,[status(thm)],[c_6,c_123])).

tff(c_10,plain,(
    ! [B_12,A_11,C_13] :
      ( r1_xboole_0(B_12,k4_xboole_0(A_11,C_13))
      | ~ r1_xboole_0(A_11,k4_xboole_0(B_12,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_139,plain,(
    ! [C_52,B_53] : r1_xboole_0(k3_xboole_0(C_52,B_53),k4_xboole_0(C_52,B_53)) ),
    inference(resolution,[status(thm)],[c_136,c_10])).

tff(c_12,plain,(
    ~ r1_xboole_0(k3_xboole_0('#skF_1','#skF_2'),k4_xboole_0('#skF_1','#skF_2')) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_142,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_139,c_12])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n012.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 11:03:52 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.67/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.13  
% 1.67/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.13  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > #nlpp > #skF_2 > #skF_1
% 1.67/1.13  
% 1.67/1.13  %Foreground sorts:
% 1.67/1.13  
% 1.67/1.13  
% 1.67/1.13  %Background operators:
% 1.67/1.13  
% 1.67/1.13  
% 1.67/1.13  %Foreground operators:
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.67/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.67/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.67/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.67/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.67/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.67/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.67/1.13  
% 1.67/1.14  tff(f_37, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 1.67/1.14  tff(f_35, axiom, (![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(k3_xboole_0(C, A), k3_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t76_xboole_1)).
% 1.67/1.14  tff(f_41, axiom, (![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_xboole_1)).
% 1.67/1.14  tff(f_31, axiom, (![A, B]: ~(~r1_xboole_0(A, B) & r1_xboole_0(k3_xboole_0(A, B), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t75_xboole_1)).
% 1.67/1.14  tff(f_45, axiom, (![A, B, C]: (r1_xboole_0(A, k4_xboole_0(B, C)) => r1_xboole_0(B, k4_xboole_0(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t81_xboole_1)).
% 1.67/1.14  tff(f_48, negated_conjecture, ~(![A, B]: r1_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t89_xboole_1)).
% 1.67/1.14  tff(c_6, plain, (![A_6, B_7]: (r1_xboole_0(k4_xboole_0(A_6, B_7), B_7))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.67/1.14  tff(c_4, plain, (![C_5, A_3, B_4]: (r1_xboole_0(k3_xboole_0(C_5, A_3), k3_xboole_0(C_5, B_4)) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.67/1.14  tff(c_15, plain, (![A_18, B_19, C_20]: (r1_xboole_0(A_18, k4_xboole_0(B_19, C_20)) | ~r1_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_41])).
% 1.67/1.14  tff(c_2, plain, (![A_1, B_2]: (~r1_xboole_0(k3_xboole_0(A_1, B_2), B_2) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.67/1.14  tff(c_70, plain, (![A_35, B_36, C_37]: (r1_xboole_0(A_35, k4_xboole_0(B_36, C_37)) | ~r1_xboole_0(k3_xboole_0(A_35, k4_xboole_0(B_36, C_37)), B_36))), inference(resolution, [status(thm)], [c_15, c_2])).
% 1.67/1.14  tff(c_123, plain, (![C_49, B_50, C_51]: (r1_xboole_0(C_49, k4_xboole_0(k3_xboole_0(C_49, B_50), C_51)) | ~r1_xboole_0(k4_xboole_0(k3_xboole_0(C_49, B_50), C_51), B_50))), inference(resolution, [status(thm)], [c_4, c_70])).
% 1.67/1.14  tff(c_136, plain, (![C_52, B_53]: (r1_xboole_0(C_52, k4_xboole_0(k3_xboole_0(C_52, B_53), B_53)))), inference(resolution, [status(thm)], [c_6, c_123])).
% 1.67/1.14  tff(c_10, plain, (![B_12, A_11, C_13]: (r1_xboole_0(B_12, k4_xboole_0(A_11, C_13)) | ~r1_xboole_0(A_11, k4_xboole_0(B_12, C_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.67/1.14  tff(c_139, plain, (![C_52, B_53]: (r1_xboole_0(k3_xboole_0(C_52, B_53), k4_xboole_0(C_52, B_53)))), inference(resolution, [status(thm)], [c_136, c_10])).
% 1.67/1.14  tff(c_12, plain, (~r1_xboole_0(k3_xboole_0('#skF_1', '#skF_2'), k4_xboole_0('#skF_1', '#skF_2'))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.67/1.14  tff(c_142, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_139, c_12])).
% 1.67/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.67/1.14  
% 1.67/1.14  Inference rules
% 1.67/1.14  ----------------------
% 1.67/1.14  #Ref     : 0
% 1.67/1.14  #Sup     : 27
% 1.67/1.14  #Fact    : 0
% 1.67/1.14  #Define  : 0
% 1.67/1.14  #Split   : 0
% 1.67/1.14  #Chain   : 0
% 1.67/1.14  #Close   : 0
% 1.67/1.14  
% 1.67/1.14  Ordering : KBO
% 1.67/1.14  
% 1.67/1.14  Simplification rules
% 1.67/1.14  ----------------------
% 1.67/1.14  #Subsume      : 1
% 1.67/1.14  #Demod        : 2
% 1.67/1.14  #Tautology    : 1
% 1.67/1.14  #SimpNegUnit  : 0
% 1.67/1.14  #BackRed      : 1
% 1.67/1.14  
% 1.67/1.14  #Partial instantiations: 0
% 1.67/1.14  #Strategies tried      : 1
% 1.67/1.14  
% 1.67/1.14  Timing (in seconds)
% 1.67/1.14  ----------------------
% 1.67/1.15  Preprocessing        : 0.24
% 1.67/1.15  Parsing              : 0.14
% 1.67/1.15  CNF conversion       : 0.01
% 1.67/1.15  Main loop            : 0.15
% 1.67/1.15  Inferencing          : 0.06
% 1.67/1.15  Reduction            : 0.03
% 1.67/1.15  Demodulation         : 0.03
% 1.67/1.15  BG Simplification    : 0.01
% 1.67/1.15  Subsumption          : 0.04
% 1.67/1.15  Abstraction          : 0.01
% 1.67/1.15  MUC search           : 0.00
% 1.67/1.15  Cooper               : 0.00
% 1.67/1.15  Total                : 0.43
% 1.67/1.15  Index Insertion      : 0.00
% 1.67/1.15  Index Deletion       : 0.00
% 1.67/1.15  Index Matching       : 0.00
% 1.67/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

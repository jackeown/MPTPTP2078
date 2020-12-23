%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:56 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.56s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   18 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   48 (  58 expanded)
%              Number of equality atoms :   14 (  16 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_35,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t37_xboole_1)).

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r1_tarski(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,C) )
       => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t73_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( ~ v1_xboole_0(C)
     => ~ ( r1_tarski(C,A)
          & r1_tarski(C,B)
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t68_xboole_1)).

tff(f_29,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(c_21,plain,(
    ! [A_15,B_16] :
      ( r1_tarski(A_15,B_16)
      | k4_xboole_0(A_15,B_16) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_14,plain,(
    ~ r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_25,plain,(
    k4_xboole_0('#skF_1','#skF_2') != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_21,c_14])).

tff(c_18,plain,(
    r1_tarski('#skF_1',k2_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_96,plain,(
    ! [A_21,B_22,C_23] :
      ( r1_tarski(k4_xboole_0(A_21,B_22),C_23)
      | ~ r1_tarski(A_21,k2_xboole_0(B_22,C_23)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_8,plain,(
    ! [A_4,B_5] :
      ( k4_xboole_0(A_4,B_5) = k1_xboole_0
      | ~ r1_tarski(A_4,B_5) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_275,plain,(
    ! [A_44,B_45,C_46] :
      ( k4_xboole_0(k4_xboole_0(A_44,B_45),C_46) = k1_xboole_0
      | ~ r1_tarski(A_44,k2_xboole_0(B_45,C_46)) ) ),
    inference(resolution,[status(thm)],[c_96,c_8])).

tff(c_294,plain,(
    k4_xboole_0(k4_xboole_0('#skF_1','#skF_2'),'#skF_3') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_275])).

tff(c_4,plain,(
    ! [A_2,B_3] : r1_tarski(k4_xboole_0(A_2,B_3),A_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_6,plain,(
    ! [A_4,B_5] :
      ( r1_tarski(A_4,B_5)
      | k4_xboole_0(A_4,B_5) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    r1_xboole_0('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_188,plain,(
    ! [A_32,B_33,C_34] :
      ( ~ r1_xboole_0(A_32,B_33)
      | ~ r1_tarski(C_34,B_33)
      | ~ r1_tarski(C_34,A_32)
      | v1_xboole_0(C_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_192,plain,(
    ! [C_35] :
      ( ~ r1_tarski(C_35,'#skF_3')
      | ~ r1_tarski(C_35,'#skF_1')
      | v1_xboole_0(C_35) ) ),
    inference(resolution,[status(thm)],[c_16,c_188])).

tff(c_208,plain,(
    ! [A_36] :
      ( ~ r1_tarski(A_36,'#skF_1')
      | v1_xboole_0(A_36)
      | k4_xboole_0(A_36,'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_6,c_192])).

tff(c_346,plain,(
    ! [B_50] :
      ( v1_xboole_0(k4_xboole_0('#skF_1',B_50))
      | k4_xboole_0(k4_xboole_0('#skF_1',B_50),'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_208])).

tff(c_2,plain,(
    ! [A_1] :
      ( k1_xboole_0 = A_1
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_513,plain,(
    ! [B_67] :
      ( k4_xboole_0('#skF_1',B_67) = k1_xboole_0
      | k4_xboole_0(k4_xboole_0('#skF_1',B_67),'#skF_3') != k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_346,c_2])).

tff(c_520,plain,(
    k4_xboole_0('#skF_1','#skF_2') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_513])).

tff(c_528,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_25,c_520])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 13:21:53 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.33  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.33  
% 2.17/1.33  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.17/1.33  %$ r1_xboole_0 > r1_tarski > v1_xboole_0 > k4_xboole_0 > k2_xboole_0 > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 2.17/1.33  
% 2.17/1.33  %Foreground sorts:
% 2.17/1.33  
% 2.17/1.33  
% 2.17/1.33  %Background operators:
% 2.17/1.33  
% 2.17/1.33  
% 2.17/1.33  %Foreground operators:
% 2.17/1.33  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.33  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.17/1.33  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.17/1.33  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.33  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.17/1.33  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.33  tff('#skF_3', type, '#skF_3': $i).
% 2.17/1.33  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.33  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.33  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.33  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.33  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.17/1.33  
% 2.56/1.34  tff(f_35, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t37_xboole_1)).
% 2.56/1.34  tff(f_56, negated_conjecture, ~(![A, B, C]: ((r1_tarski(A, k2_xboole_0(B, C)) & r1_xboole_0(A, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t73_xboole_1)).
% 2.56/1.34  tff(f_39, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 2.56/1.34  tff(f_31, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 2.56/1.34  tff(f_49, axiom, (![A, B, C]: (~v1_xboole_0(C) => ~((r1_tarski(C, A) & r1_tarski(C, B)) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t68_xboole_1)).
% 2.56/1.34  tff(f_29, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 2.56/1.34  tff(c_21, plain, (![A_15, B_16]: (r1_tarski(A_15, B_16) | k4_xboole_0(A_15, B_16)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.56/1.34  tff(c_14, plain, (~r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.56/1.34  tff(c_25, plain, (k4_xboole_0('#skF_1', '#skF_2')!=k1_xboole_0), inference(resolution, [status(thm)], [c_21, c_14])).
% 2.56/1.34  tff(c_18, plain, (r1_tarski('#skF_1', k2_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.56/1.34  tff(c_96, plain, (![A_21, B_22, C_23]: (r1_tarski(k4_xboole_0(A_21, B_22), C_23) | ~r1_tarski(A_21, k2_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.56/1.34  tff(c_8, plain, (![A_4, B_5]: (k4_xboole_0(A_4, B_5)=k1_xboole_0 | ~r1_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.56/1.34  tff(c_275, plain, (![A_44, B_45, C_46]: (k4_xboole_0(k4_xboole_0(A_44, B_45), C_46)=k1_xboole_0 | ~r1_tarski(A_44, k2_xboole_0(B_45, C_46)))), inference(resolution, [status(thm)], [c_96, c_8])).
% 2.56/1.34  tff(c_294, plain, (k4_xboole_0(k4_xboole_0('#skF_1', '#skF_2'), '#skF_3')=k1_xboole_0), inference(resolution, [status(thm)], [c_18, c_275])).
% 2.56/1.34  tff(c_4, plain, (![A_2, B_3]: (r1_tarski(k4_xboole_0(A_2, B_3), A_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.56/1.34  tff(c_6, plain, (![A_4, B_5]: (r1_tarski(A_4, B_5) | k4_xboole_0(A_4, B_5)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.56/1.34  tff(c_16, plain, (r1_xboole_0('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.56/1.34  tff(c_188, plain, (![A_32, B_33, C_34]: (~r1_xboole_0(A_32, B_33) | ~r1_tarski(C_34, B_33) | ~r1_tarski(C_34, A_32) | v1_xboole_0(C_34))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.56/1.34  tff(c_192, plain, (![C_35]: (~r1_tarski(C_35, '#skF_3') | ~r1_tarski(C_35, '#skF_1') | v1_xboole_0(C_35))), inference(resolution, [status(thm)], [c_16, c_188])).
% 2.56/1.34  tff(c_208, plain, (![A_36]: (~r1_tarski(A_36, '#skF_1') | v1_xboole_0(A_36) | k4_xboole_0(A_36, '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_6, c_192])).
% 2.56/1.34  tff(c_346, plain, (![B_50]: (v1_xboole_0(k4_xboole_0('#skF_1', B_50)) | k4_xboole_0(k4_xboole_0('#skF_1', B_50), '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_208])).
% 2.56/1.34  tff(c_2, plain, (![A_1]: (k1_xboole_0=A_1 | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.56/1.34  tff(c_513, plain, (![B_67]: (k4_xboole_0('#skF_1', B_67)=k1_xboole_0 | k4_xboole_0(k4_xboole_0('#skF_1', B_67), '#skF_3')!=k1_xboole_0)), inference(resolution, [status(thm)], [c_346, c_2])).
% 2.56/1.34  tff(c_520, plain, (k4_xboole_0('#skF_1', '#skF_2')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_294, c_513])).
% 2.56/1.34  tff(c_528, plain, $false, inference(negUnitSimplification, [status(thm)], [c_25, c_520])).
% 2.56/1.34  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.56/1.34  
% 2.56/1.34  Inference rules
% 2.56/1.34  ----------------------
% 2.56/1.34  #Ref     : 0
% 2.56/1.34  #Sup     : 133
% 2.56/1.34  #Fact    : 0
% 2.56/1.34  #Define  : 0
% 2.56/1.34  #Split   : 1
% 2.56/1.34  #Chain   : 0
% 2.56/1.34  #Close   : 0
% 2.56/1.34  
% 2.56/1.34  Ordering : KBO
% 2.56/1.34  
% 2.56/1.34  Simplification rules
% 2.56/1.34  ----------------------
% 2.56/1.34  #Subsume      : 16
% 2.56/1.34  #Demod        : 36
% 2.56/1.34  #Tautology    : 54
% 2.56/1.34  #SimpNegUnit  : 1
% 2.56/1.34  #BackRed      : 0
% 2.56/1.34  
% 2.56/1.34  #Partial instantiations: 0
% 2.56/1.34  #Strategies tried      : 1
% 2.56/1.34  
% 2.56/1.34  Timing (in seconds)
% 2.56/1.34  ----------------------
% 2.56/1.35  Preprocessing        : 0.27
% 2.56/1.35  Parsing              : 0.15
% 2.56/1.35  CNF conversion       : 0.02
% 2.56/1.35  Main loop            : 0.32
% 2.56/1.35  Inferencing          : 0.13
% 2.56/1.35  Reduction            : 0.09
% 2.56/1.35  Demodulation         : 0.06
% 2.56/1.35  BG Simplification    : 0.02
% 2.56/1.35  Subsumption          : 0.07
% 2.56/1.35  Abstraction          : 0.01
% 2.56/1.35  MUC search           : 0.00
% 2.56/1.35  Cooper               : 0.00
% 2.56/1.35  Total                : 0.61
% 2.56/1.35  Index Insertion      : 0.00
% 2.56/1.35  Index Deletion       : 0.00
% 2.56/1.35  Index Matching       : 0.00
% 2.56/1.35  BG Taut test         : 0.00
%------------------------------------------------------------------------------

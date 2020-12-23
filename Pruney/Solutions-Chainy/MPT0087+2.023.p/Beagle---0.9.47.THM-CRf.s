%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n010.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:44:20 EST 2020

% Result     : Theorem 1.51s
% Output     : CNFRefutation 1.51s
% Verified   : 
% Statistics : Number of formulae       :   20 (  21 expanded)
%              Number of leaves         :   13 (  14 expanded)
%              Depth                    :    4
%              Number of atoms          :   18 (  20 expanded)
%              Number of equality atoms :    2 (   2 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_xboole_0(A,B)
       => r1_xboole_0(A,k4_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t80_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_14,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(k3_xboole_0(A_3,B_4),k4_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_42,plain,(
    ! [A_12,C_13,B_14] :
      ( r1_xboole_0(A_12,C_13)
      | ~ r1_xboole_0(A_12,k2_xboole_0(B_14,C_13)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_50,plain,(
    ! [A_18,A_19,B_20] :
      ( r1_xboole_0(A_18,k4_xboole_0(A_19,B_20))
      | ~ r1_xboole_0(A_18,A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_42])).

tff(c_12,plain,(
    ~ r1_xboole_0('#skF_1',k4_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_53,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_50,c_12])).

tff(c_60,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_53])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n010.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:24:29 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.19/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.51/1.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.13  
% 1.51/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.13  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.51/1.13  
% 1.51/1.13  %Foreground sorts:
% 1.51/1.13  
% 1.51/1.13  
% 1.51/1.13  %Background operators:
% 1.51/1.13  
% 1.51/1.13  
% 1.51/1.13  %Foreground operators:
% 1.51/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.51/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.51/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.51/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.51/1.13  tff('#skF_3', type, '#skF_3': $i).
% 1.51/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.51/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.51/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.51/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.51/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.51/1.13  
% 1.51/1.13  tff(f_50, negated_conjecture, ~(![A, B, C]: (r1_xboole_0(A, B) => r1_xboole_0(A, k4_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t80_xboole_1)).
% 1.51/1.13  tff(f_29, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 1.51/1.13  tff(f_45, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_xboole_1)).
% 1.51/1.13  tff(c_14, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.51/1.13  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(k3_xboole_0(A_3, B_4), k4_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.51/1.13  tff(c_42, plain, (![A_12, C_13, B_14]: (r1_xboole_0(A_12, C_13) | ~r1_xboole_0(A_12, k2_xboole_0(B_14, C_13)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.51/1.13  tff(c_50, plain, (![A_18, A_19, B_20]: (r1_xboole_0(A_18, k4_xboole_0(A_19, B_20)) | ~r1_xboole_0(A_18, A_19))), inference(superposition, [status(thm), theory('equality')], [c_4, c_42])).
% 1.51/1.13  tff(c_12, plain, (~r1_xboole_0('#skF_1', k4_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.51/1.13  tff(c_53, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_50, c_12])).
% 1.51/1.13  tff(c_60, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_53])).
% 1.51/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.51/1.13  
% 1.51/1.13  Inference rules
% 1.51/1.13  ----------------------
% 1.51/1.13  #Ref     : 0
% 1.51/1.13  #Sup     : 11
% 1.51/1.13  #Fact    : 0
% 1.51/1.13  #Define  : 0
% 1.51/1.13  #Split   : 0
% 1.51/1.13  #Chain   : 0
% 1.51/1.13  #Close   : 0
% 1.51/1.13  
% 1.51/1.13  Ordering : KBO
% 1.51/1.13  
% 1.51/1.13  Simplification rules
% 1.51/1.13  ----------------------
% 1.51/1.13  #Subsume      : 0
% 1.51/1.13  #Demod        : 1
% 1.51/1.13  #Tautology    : 4
% 1.51/1.13  #SimpNegUnit  : 0
% 1.51/1.13  #BackRed      : 0
% 1.51/1.13  
% 1.51/1.13  #Partial instantiations: 0
% 1.51/1.13  #Strategies tried      : 1
% 1.51/1.13  
% 1.51/1.13  Timing (in seconds)
% 1.51/1.13  ----------------------
% 1.51/1.14  Preprocessing        : 0.26
% 1.51/1.14  Parsing              : 0.15
% 1.51/1.14  CNF conversion       : 0.02
% 1.51/1.14  Main loop            : 0.08
% 1.51/1.14  Inferencing          : 0.04
% 1.51/1.14  Reduction            : 0.02
% 1.51/1.14  Demodulation         : 0.02
% 1.51/1.14  BG Simplification    : 0.01
% 1.51/1.14  Subsumption          : 0.01
% 1.51/1.14  Abstraction          : 0.00
% 1.51/1.14  MUC search           : 0.00
% 1.51/1.14  Cooper               : 0.00
% 1.51/1.14  Total                : 0.37
% 1.51/1.14  Index Insertion      : 0.00
% 1.51/1.14  Index Deletion       : 0.00
% 1.51/1.14  Index Matching       : 0.00
% 1.51/1.14  BG Taut test         : 0.00
%------------------------------------------------------------------------------

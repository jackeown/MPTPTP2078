%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:43:59 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
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

tff(f_52,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r1_xboole_0(A,k3_xboole_0(B,C))
          & r1_xboole_0(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ~ ( ~ r1_xboole_0(A,k2_xboole_0(B,C))
          & r1_xboole_0(A,B)
          & r1_xboole_0(A,C) )
      & ~ ( ~ ( r1_xboole_0(A,B)
              & r1_xboole_0(A,C) )
          & r1_xboole_0(A,k2_xboole_0(B,C)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_xboole_1)).

tff(c_12,plain,(
    r1_xboole_0('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_2,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_28,plain,(
    ! [A_13,C_14,B_15] :
      ( r1_xboole_0(A_13,C_14)
      | ~ r1_xboole_0(A_13,k2_xboole_0(B_15,C_14)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_47,plain,(
    ! [A_18,A_19,B_20] :
      ( r1_xboole_0(A_18,k3_xboole_0(A_19,B_20))
      | ~ r1_xboole_0(A_18,A_19) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_28])).

tff(c_14,plain,(
    ~ r1_xboole_0('#skF_1',k3_xboole_0('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_50,plain,(
    ~ r1_xboole_0('#skF_1','#skF_2') ),
    inference(resolution,[status(thm)],[c_47,c_14])).

tff(c_54,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:51:45 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.06  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.06  
% 1.58/1.06  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.06  %$ r1_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > #skF_2 > #skF_3 > #skF_1
% 1.58/1.06  
% 1.58/1.06  %Foreground sorts:
% 1.58/1.06  
% 1.58/1.06  
% 1.58/1.06  %Background operators:
% 1.58/1.06  
% 1.58/1.06  
% 1.58/1.06  %Foreground operators:
% 1.58/1.06  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.06  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.58/1.06  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.58/1.06  tff('#skF_2', type, '#skF_2': $i).
% 1.58/1.06  tff('#skF_3', type, '#skF_3': $i).
% 1.58/1.06  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.06  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.06  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.06  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.58/1.06  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.58/1.06  
% 1.58/1.07  tff(f_52, negated_conjecture, ~(![A, B, C]: ~(~r1_xboole_0(A, k3_xboole_0(B, C)) & r1_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_xboole_1)).
% 1.58/1.07  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t22_xboole_1)).
% 1.58/1.07  tff(f_45, axiom, (![A, B, C]: (~((~r1_xboole_0(A, k2_xboole_0(B, C)) & r1_xboole_0(A, B)) & r1_xboole_0(A, C)) & ~(~(r1_xboole_0(A, B) & r1_xboole_0(A, C)) & r1_xboole_0(A, k2_xboole_0(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_xboole_1)).
% 1.58/1.07  tff(c_12, plain, (r1_xboole_0('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.58/1.07  tff(c_2, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(A_1, B_2))=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.58/1.07  tff(c_28, plain, (![A_13, C_14, B_15]: (r1_xboole_0(A_13, C_14) | ~r1_xboole_0(A_13, k2_xboole_0(B_15, C_14)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 1.58/1.07  tff(c_47, plain, (![A_18, A_19, B_20]: (r1_xboole_0(A_18, k3_xboole_0(A_19, B_20)) | ~r1_xboole_0(A_18, A_19))), inference(superposition, [status(thm), theory('equality')], [c_2, c_28])).
% 1.58/1.07  tff(c_14, plain, (~r1_xboole_0('#skF_1', k3_xboole_0('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_52])).
% 1.58/1.07  tff(c_50, plain, (~r1_xboole_0('#skF_1', '#skF_2')), inference(resolution, [status(thm)], [c_47, c_14])).
% 1.58/1.07  tff(c_54, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_50])).
% 1.58/1.07  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.58/1.07  
% 1.58/1.07  Inference rules
% 1.58/1.07  ----------------------
% 1.58/1.07  #Ref     : 0
% 1.58/1.07  #Sup     : 9
% 1.58/1.07  #Fact    : 0
% 1.58/1.07  #Define  : 0
% 1.58/1.07  #Split   : 0
% 1.58/1.07  #Chain   : 0
% 1.58/1.07  #Close   : 0
% 1.58/1.07  
% 1.58/1.07  Ordering : KBO
% 1.58/1.07  
% 1.58/1.07  Simplification rules
% 1.58/1.07  ----------------------
% 1.58/1.07  #Subsume      : 0
% 1.58/1.07  #Demod        : 1
% 1.58/1.07  #Tautology    : 5
% 1.58/1.07  #SimpNegUnit  : 0
% 1.58/1.07  #BackRed      : 0
% 1.58/1.07  
% 1.58/1.07  #Partial instantiations: 0
% 1.58/1.07  #Strategies tried      : 1
% 1.58/1.07  
% 1.58/1.07  Timing (in seconds)
% 1.58/1.07  ----------------------
% 1.58/1.07  Preprocessing        : 0.25
% 1.58/1.07  Parsing              : 0.14
% 1.58/1.07  CNF conversion       : 0.01
% 1.58/1.07  Main loop            : 0.08
% 1.58/1.07  Inferencing          : 0.04
% 1.58/1.07  Reduction            : 0.02
% 1.58/1.07  Demodulation         : 0.02
% 1.58/1.07  BG Simplification    : 0.01
% 1.58/1.08  Subsumption          : 0.01
% 1.58/1.08  Abstraction          : 0.00
% 1.58/1.08  MUC search           : 0.00
% 1.58/1.08  Cooper               : 0.00
% 1.58/1.08  Total                : 0.35
% 1.58/1.08  Index Insertion      : 0.00
% 1.58/1.08  Index Deletion       : 0.00
% 1.58/1.08  Index Matching       : 0.00
% 1.58/1.08  BG Taut test         : 0.00
%------------------------------------------------------------------------------

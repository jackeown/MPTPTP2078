%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:53 EST 2020

% Result     : Theorem 1.61s
% Output     : CNFRefutation 1.61s
% Verified   : 
% Statistics : Number of formulae       :   22 (  23 expanded)
%              Number of leaves         :   15 (  16 expanded)
%              Depth                    :    4
%              Number of atoms          :   15 (  17 expanded)
%              Number of equality atoms :    9 (  11 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( A != B
       => k4_xboole_0(k2_xboole_0(C,k1_tarski(A)),k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C,k1_tarski(B)),k1_tarski(A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t147_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t87_xboole_1)).

tff(c_12,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(k1_tarski(A_8),k1_tarski(B_9))
      | B_9 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_4,plain,(
    ! [C_5,B_4,A_3] :
      ( k4_xboole_0(k2_xboole_0(C_5,B_4),A_3) = k2_xboole_0(k4_xboole_0(C_5,A_3),B_4)
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k1_tarski('#skF_1')),k1_tarski('#skF_2')) != k2_xboole_0(k4_xboole_0('#skF_3',k1_tarski('#skF_2')),k1_tarski('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_47,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_10])).

tff(c_50,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_8,c_47])).

tff(c_54,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n019.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:04:52 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.61/1.14  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.15  
% 1.61/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.15  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.61/1.15  
% 1.61/1.15  %Foreground sorts:
% 1.61/1.15  
% 1.61/1.15  
% 1.61/1.15  %Background operators:
% 1.61/1.15  
% 1.61/1.15  
% 1.61/1.15  %Foreground operators:
% 1.61/1.15  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.61/1.15  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.61/1.15  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.61/1.15  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.61/1.15  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.61/1.15  tff('#skF_2', type, '#skF_2': $i).
% 1.61/1.15  tff('#skF_3', type, '#skF_3': $i).
% 1.61/1.15  tff('#skF_1', type, '#skF_1': $i).
% 1.61/1.15  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.61/1.15  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.61/1.15  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.61/1.15  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.61/1.15  
% 1.61/1.15  tff(f_44, negated_conjecture, ~(![A, B, C]: (~(A = B) => (k4_xboole_0(k2_xboole_0(C, k1_tarski(A)), k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C, k1_tarski(B)), k1_tarski(A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t147_zfmisc_1)).
% 1.61/1.15  tff(f_38, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.61/1.15  tff(f_31, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t87_xboole_1)).
% 1.61/1.15  tff(c_12, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.61/1.15  tff(c_8, plain, (![A_8, B_9]: (r1_xboole_0(k1_tarski(A_8), k1_tarski(B_9)) | B_9=A_8)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.61/1.15  tff(c_4, plain, (![C_5, B_4, A_3]: (k4_xboole_0(k2_xboole_0(C_5, B_4), A_3)=k2_xboole_0(k4_xboole_0(C_5, A_3), B_4) | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.61/1.15  tff(c_10, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k1_tarski('#skF_1')), k1_tarski('#skF_2'))!=k2_xboole_0(k4_xboole_0('#skF_3', k1_tarski('#skF_2')), k1_tarski('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.61/1.15  tff(c_47, plain, (~r1_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_4, c_10])).
% 1.61/1.15  tff(c_50, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_8, c_47])).
% 1.61/1.15  tff(c_54, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_50])).
% 1.61/1.15  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.61/1.15  
% 1.61/1.15  Inference rules
% 1.61/1.15  ----------------------
% 1.61/1.15  #Ref     : 0
% 1.61/1.15  #Sup     : 9
% 1.61/1.15  #Fact    : 0
% 1.61/1.15  #Define  : 0
% 1.61/1.15  #Split   : 0
% 1.61/1.15  #Chain   : 0
% 1.61/1.15  #Close   : 0
% 1.61/1.15  
% 1.61/1.15  Ordering : KBO
% 1.61/1.15  
% 1.61/1.15  Simplification rules
% 1.61/1.15  ----------------------
% 1.61/1.15  #Subsume      : 0
% 1.61/1.15  #Demod        : 0
% 1.61/1.15  #Tautology    : 6
% 1.61/1.15  #SimpNegUnit  : 1
% 1.61/1.15  #BackRed      : 0
% 1.61/1.15  
% 1.61/1.15  #Partial instantiations: 0
% 1.61/1.15  #Strategies tried      : 1
% 1.61/1.15  
% 1.61/1.15  Timing (in seconds)
% 1.61/1.15  ----------------------
% 1.61/1.16  Preprocessing        : 0.26
% 1.61/1.16  Parsing              : 0.13
% 1.61/1.16  CNF conversion       : 0.01
% 1.61/1.16  Main loop            : 0.07
% 1.61/1.16  Inferencing          : 0.03
% 1.61/1.16  Reduction            : 0.02
% 1.61/1.16  Demodulation         : 0.01
% 1.61/1.16  BG Simplification    : 0.01
% 1.61/1.16  Subsumption          : 0.01
% 1.61/1.16  Abstraction          : 0.00
% 1.61/1.16  MUC search           : 0.00
% 1.61/1.16  Cooper               : 0.00
% 1.61/1.16  Total                : 0.35
% 1.61/1.16  Index Insertion      : 0.00
% 1.61/1.16  Index Deletion       : 0.00
% 1.61/1.16  Index Matching       : 0.00
% 1.61/1.16  BG Taut test         : 0.00
%------------------------------------------------------------------------------

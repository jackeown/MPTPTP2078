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
% DateTime   : Thu Dec  3 09:54:53 EST 2020

% Result     : Theorem 1.58s
% Output     : CNFRefutation 1.58s
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
%$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

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

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff(f_44,negated_conjecture,(
    ~ ! [A,B,C] :
        ( A != B
       => k4_xboole_0(k2_xboole_0(C,k1_tarski(A)),k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C,k1_tarski(B)),k1_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

tff(c_12,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( r1_xboole_0(k1_tarski(A_7),k1_tarski(B_8))
      | B_8 = A_7 ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_2,plain,(
    ! [C_3,B_2,A_1] :
      ( k4_xboole_0(k2_xboole_0(C_3,B_2),A_1) = k2_xboole_0(k4_xboole_0(C_3,A_1),B_2)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k1_tarski('#skF_1')),k1_tarski('#skF_2')) != k2_xboole_0(k4_xboole_0('#skF_3',k1_tarski('#skF_2')),k1_tarski('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_47,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10])).

tff(c_50,plain,(
    '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_8,c_47])).

tff(c_54,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_50])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 12:25:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.58/1.09  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.09  
% 1.58/1.09  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.09  %$ r1_xboole_0 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.58/1.09  
% 1.58/1.09  %Foreground sorts:
% 1.58/1.09  
% 1.58/1.09  
% 1.58/1.09  %Background operators:
% 1.58/1.09  
% 1.58/1.09  
% 1.58/1.09  %Foreground operators:
% 1.58/1.09  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.58/1.09  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.58/1.09  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.58/1.09  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.58/1.09  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.58/1.09  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.58/1.09  tff('#skF_2', type, '#skF_2': $i).
% 1.58/1.09  tff('#skF_3', type, '#skF_3': $i).
% 1.58/1.09  tff('#skF_1', type, '#skF_1': $i).
% 1.58/1.09  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.58/1.09  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.58/1.09  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.58/1.09  
% 1.58/1.10  tff(f_44, negated_conjecture, ~(![A, B, C]: (~(A = B) => (k4_xboole_0(k2_xboole_0(C, k1_tarski(A)), k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C, k1_tarski(B)), k1_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_zfmisc_1)).
% 1.58/1.10  tff(f_38, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.58/1.10  tff(f_29, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_xboole_1)).
% 1.58/1.10  tff(c_12, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.58/1.10  tff(c_8, plain, (![A_7, B_8]: (r1_xboole_0(k1_tarski(A_7), k1_tarski(B_8)) | B_8=A_7)), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.58/1.10  tff(c_2, plain, (![C_3, B_2, A_1]: (k4_xboole_0(k2_xboole_0(C_3, B_2), A_1)=k2_xboole_0(k4_xboole_0(C_3, A_1), B_2) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.58/1.10  tff(c_10, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k1_tarski('#skF_1')), k1_tarski('#skF_2'))!=k2_xboole_0(k4_xboole_0('#skF_3', k1_tarski('#skF_2')), k1_tarski('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.58/1.10  tff(c_47, plain, (~r1_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_2, c_10])).
% 1.58/1.10  tff(c_50, plain, ('#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_8, c_47])).
% 1.58/1.10  tff(c_54, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_50])).
% 1.58/1.10  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.58/1.10  
% 1.58/1.10  Inference rules
% 1.58/1.10  ----------------------
% 1.58/1.10  #Ref     : 0
% 1.58/1.10  #Sup     : 9
% 1.58/1.10  #Fact    : 0
% 1.58/1.10  #Define  : 0
% 1.58/1.10  #Split   : 0
% 1.58/1.10  #Chain   : 0
% 1.58/1.10  #Close   : 0
% 1.58/1.10  
% 1.58/1.10  Ordering : KBO
% 1.58/1.10  
% 1.58/1.10  Simplification rules
% 1.58/1.10  ----------------------
% 1.58/1.10  #Subsume      : 0
% 1.58/1.10  #Demod        : 0
% 1.58/1.10  #Tautology    : 6
% 1.58/1.10  #SimpNegUnit  : 1
% 1.58/1.10  #BackRed      : 0
% 1.58/1.10  
% 1.58/1.10  #Partial instantiations: 0
% 1.58/1.10  #Strategies tried      : 1
% 1.58/1.10  
% 1.58/1.10  Timing (in seconds)
% 1.58/1.10  ----------------------
% 1.58/1.10  Preprocessing        : 0.26
% 1.58/1.10  Parsing              : 0.14
% 1.58/1.10  CNF conversion       : 0.01
% 1.58/1.10  Main loop            : 0.07
% 1.58/1.10  Inferencing          : 0.04
% 1.58/1.10  Reduction            : 0.02
% 1.58/1.10  Demodulation         : 0.01
% 1.58/1.10  BG Simplification    : 0.01
% 1.58/1.10  Subsumption          : 0.01
% 1.58/1.10  Abstraction          : 0.00
% 1.58/1.10  MUC search           : 0.00
% 1.58/1.10  Cooper               : 0.00
% 1.58/1.10  Total                : 0.35
% 1.58/1.10  Index Insertion      : 0.00
% 1.58/1.10  Index Deletion       : 0.00
% 1.58/1.10  Index Matching       : 0.00
% 1.58/1.10  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:42 EST 2020

% Result     : Theorem 2.06s
% Output     : CNFRefutation 2.06s
% Verified   : 
% Statistics : Number of formulae       :   40 (  47 expanded)
%              Number of leaves         :   23 (  27 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  50 expanded)
%              Number of equality atoms :    6 (  10 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_66,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_36,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_6,plain,(
    ! [B_2] : r1_tarski(B_2,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_3,C_5,B_4] :
      ( r1_tarski(A_3,k2_xboole_0(C_5,B_4))
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_38,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_97,plain,(
    ! [B_55,A_56] :
      ( B_55 = A_56
      | ~ r1_tarski(B_55,A_56)
      | ~ r1_tarski(A_56,B_55) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,
    ( k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2'
    | ~ r1_tarski('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(resolution,[status(thm)],[c_38,c_97])).

tff(c_192,plain,(
    ~ r1_tarski('#skF_2',k2_xboole_0(k1_tarski('#skF_1'),'#skF_2')) ),
    inference(splitLeft,[status(thm)],[c_107])).

tff(c_195,plain,(
    ~ r1_tarski('#skF_2','#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_192])).

tff(c_199,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_195])).

tff(c_200,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_107])).

tff(c_14,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_6,B_7] : r1_tarski(A_6,k2_xboole_0(A_6,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_113,plain,(
    ! [A_57,C_58,B_59] :
      ( r2_hidden(A_57,C_58)
      | ~ r1_tarski(k2_tarski(A_57,B_59),C_58) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_137,plain,(
    ! [A_63,B_64,B_65] : r2_hidden(A_63,k2_xboole_0(k2_tarski(A_63,B_64),B_65)) ),
    inference(resolution,[status(thm)],[c_10,c_113])).

tff(c_144,plain,(
    ! [A_12,B_65] : r2_hidden(A_12,k2_xboole_0(k1_tarski(A_12),B_65)) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_137])).

tff(c_210,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_200,c_144])).

tff(c_217,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_36,c_210])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:00:04 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.06/1.21  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.21  
% 2.06/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.21  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.06/1.21  
% 2.06/1.21  %Foreground sorts:
% 2.06/1.21  
% 2.06/1.21  
% 2.06/1.21  %Background operators:
% 2.06/1.21  
% 2.06/1.21  
% 2.06/1.21  %Foreground operators:
% 2.06/1.21  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.06/1.21  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.06/1.21  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.06/1.21  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.06/1.21  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.06/1.21  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.06/1.21  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.06/1.21  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.06/1.21  tff('#skF_2', type, '#skF_2': $i).
% 2.06/1.21  tff('#skF_1', type, '#skF_1': $i).
% 2.06/1.21  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.21  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.21  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.06/1.21  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.06/1.21  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.06/1.21  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.06/1.21  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.06/1.21  
% 2.06/1.22  tff(f_66, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.06/1.22  tff(f_31, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.06/1.22  tff(f_35, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 2.06/1.22  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.06/1.22  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.06/1.22  tff(f_61, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.06/1.22  tff(c_36, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.06/1.22  tff(c_6, plain, (![B_2]: (r1_tarski(B_2, B_2))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.22  tff(c_8, plain, (![A_3, C_5, B_4]: (r1_tarski(A_3, k2_xboole_0(C_5, B_4)) | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.06/1.22  tff(c_38, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.06/1.22  tff(c_97, plain, (![B_55, A_56]: (B_55=A_56 | ~r1_tarski(B_55, A_56) | ~r1_tarski(A_56, B_55))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.06/1.22  tff(c_107, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2' | ~r1_tarski('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))), inference(resolution, [status(thm)], [c_38, c_97])).
% 2.06/1.22  tff(c_192, plain, (~r1_tarski('#skF_2', k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'))), inference(splitLeft, [status(thm)], [c_107])).
% 2.06/1.22  tff(c_195, plain, (~r1_tarski('#skF_2', '#skF_2')), inference(resolution, [status(thm)], [c_8, c_192])).
% 2.06/1.22  tff(c_199, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_6, c_195])).
% 2.06/1.22  tff(c_200, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')='#skF_2'), inference(splitRight, [status(thm)], [c_107])).
% 2.06/1.22  tff(c_14, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.06/1.22  tff(c_10, plain, (![A_6, B_7]: (r1_tarski(A_6, k2_xboole_0(A_6, B_7)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.06/1.22  tff(c_113, plain, (![A_57, C_58, B_59]: (r2_hidden(A_57, C_58) | ~r1_tarski(k2_tarski(A_57, B_59), C_58))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.06/1.22  tff(c_137, plain, (![A_63, B_64, B_65]: (r2_hidden(A_63, k2_xboole_0(k2_tarski(A_63, B_64), B_65)))), inference(resolution, [status(thm)], [c_10, c_113])).
% 2.06/1.22  tff(c_144, plain, (![A_12, B_65]: (r2_hidden(A_12, k2_xboole_0(k1_tarski(A_12), B_65)))), inference(superposition, [status(thm), theory('equality')], [c_14, c_137])).
% 2.06/1.22  tff(c_210, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_200, c_144])).
% 2.06/1.22  tff(c_217, plain, $false, inference(negUnitSimplification, [status(thm)], [c_36, c_210])).
% 2.06/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.06/1.22  
% 2.06/1.22  Inference rules
% 2.06/1.22  ----------------------
% 2.06/1.22  #Ref     : 0
% 2.06/1.22  #Sup     : 39
% 2.06/1.22  #Fact    : 0
% 2.06/1.22  #Define  : 0
% 2.06/1.22  #Split   : 1
% 2.06/1.22  #Chain   : 0
% 2.06/1.22  #Close   : 0
% 2.06/1.22  
% 2.06/1.22  Ordering : KBO
% 2.06/1.22  
% 2.06/1.22  Simplification rules
% 2.06/1.22  ----------------------
% 2.06/1.22  #Subsume      : 0
% 2.06/1.22  #Demod        : 10
% 2.06/1.22  #Tautology    : 20
% 2.06/1.22  #SimpNegUnit  : 1
% 2.06/1.22  #BackRed      : 1
% 2.06/1.22  
% 2.06/1.22  #Partial instantiations: 0
% 2.06/1.22  #Strategies tried      : 1
% 2.06/1.22  
% 2.06/1.22  Timing (in seconds)
% 2.06/1.22  ----------------------
% 2.06/1.23  Preprocessing        : 0.30
% 2.06/1.23  Parsing              : 0.16
% 2.06/1.23  CNF conversion       : 0.02
% 2.06/1.23  Main loop            : 0.15
% 2.06/1.23  Inferencing          : 0.05
% 2.06/1.23  Reduction            : 0.05
% 2.06/1.23  Demodulation         : 0.04
% 2.06/1.23  BG Simplification    : 0.01
% 2.06/1.23  Subsumption          : 0.03
% 2.06/1.23  Abstraction          : 0.01
% 2.06/1.23  MUC search           : 0.00
% 2.06/1.23  Cooper               : 0.00
% 2.06/1.23  Total                : 0.47
% 2.06/1.23  Index Insertion      : 0.00
% 2.06/1.23  Index Deletion       : 0.00
% 2.06/1.23  Index Matching       : 0.00
% 2.06/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

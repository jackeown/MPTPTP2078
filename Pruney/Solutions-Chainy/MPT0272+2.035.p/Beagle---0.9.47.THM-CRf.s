%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:10 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   30 (  31 expanded)
%              Number of leaves         :   21 (  22 expanded)
%              Depth                    :    4
%              Number of atoms          :   21 (  23 expanded)
%              Number of equality atoms :   12 (  14 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff(o_0_0_xboole_0,type,(
    o_0_0_xboole_0: $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_44,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l35_zfmisc_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_28,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(c_57,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(k1_tarski(A_39),B_40) = k1_xboole_0
      | ~ r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_32,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_75,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_57,c_32])).

tff(c_4,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_28])).

tff(c_26,plain,(
    ! [B_32,C_33] :
      ( k4_xboole_0(k2_tarski(B_32,B_32),C_33) = k1_tarski(B_32)
      | r2_hidden(B_32,C_33) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_86,plain,(
    ! [B_44,C_45] :
      ( k4_xboole_0(k1_tarski(B_44),C_45) = k1_tarski(B_44)
      | r2_hidden(B_44,C_45) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_26])).

tff(c_30,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_98,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_30])).

tff(c_112,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_98])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n005.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 13:49:32 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.13  
% 1.72/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.13  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_2 > #skF_1
% 1.72/1.13  
% 1.72/1.13  %Foreground sorts:
% 1.72/1.13  
% 1.72/1.13  
% 1.72/1.13  %Background operators:
% 1.72/1.13  
% 1.72/1.13  
% 1.72/1.13  %Foreground operators:
% 1.72/1.13  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 1.72/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.72/1.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.72/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.72/1.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 1.72/1.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.72/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.72/1.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.72/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 1.72/1.13  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 1.72/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.13  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 1.72/1.13  
% 1.72/1.14  tff(f_44, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l35_zfmisc_1)).
% 1.72/1.14  tff(f_58, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 1.72/1.14  tff(f_28, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.72/1.14  tff(f_53, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 1.72/1.14  tff(c_57, plain, (![A_39, B_40]: (k4_xboole_0(k1_tarski(A_39), B_40)=k1_xboole_0 | ~r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.72/1.14  tff(c_32, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.72/1.14  tff(c_75, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_57, c_32])).
% 1.72/1.14  tff(c_4, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_28])).
% 1.72/1.14  tff(c_26, plain, (![B_32, C_33]: (k4_xboole_0(k2_tarski(B_32, B_32), C_33)=k1_tarski(B_32) | r2_hidden(B_32, C_33))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.72/1.14  tff(c_86, plain, (![B_44, C_45]: (k4_xboole_0(k1_tarski(B_44), C_45)=k1_tarski(B_44) | r2_hidden(B_44, C_45))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_26])).
% 1.72/1.14  tff(c_30, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_58])).
% 1.72/1.14  tff(c_98, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_86, c_30])).
% 1.72/1.14  tff(c_112, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_98])).
% 1.72/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.14  
% 1.72/1.14  Inference rules
% 1.72/1.14  ----------------------
% 1.72/1.14  #Ref     : 0
% 1.72/1.14  #Sup     : 20
% 1.72/1.14  #Fact    : 0
% 1.72/1.14  #Define  : 0
% 1.72/1.14  #Split   : 0
% 1.72/1.14  #Chain   : 0
% 1.72/1.14  #Close   : 0
% 1.72/1.14  
% 1.72/1.14  Ordering : KBO
% 1.72/1.14  
% 1.72/1.14  Simplification rules
% 1.72/1.14  ----------------------
% 1.72/1.14  #Subsume      : 1
% 1.72/1.14  #Demod        : 1
% 1.72/1.14  #Tautology    : 13
% 1.72/1.14  #SimpNegUnit  : 1
% 1.72/1.14  #BackRed      : 0
% 1.72/1.14  
% 1.72/1.14  #Partial instantiations: 0
% 1.72/1.14  #Strategies tried      : 1
% 1.72/1.14  
% 1.72/1.14  Timing (in seconds)
% 1.72/1.14  ----------------------
% 1.72/1.14  Preprocessing        : 0.30
% 1.72/1.14  Parsing              : 0.16
% 1.72/1.14  CNF conversion       : 0.02
% 1.72/1.14  Main loop            : 0.09
% 1.72/1.14  Inferencing          : 0.03
% 1.72/1.14  Reduction            : 0.03
% 1.72/1.14  Demodulation         : 0.02
% 1.72/1.14  BG Simplification    : 0.01
% 1.72/1.14  Subsumption          : 0.01
% 1.72/1.14  Abstraction          : 0.01
% 1.72/1.14  MUC search           : 0.00
% 1.72/1.15  Cooper               : 0.00
% 1.72/1.15  Total                : 0.41
% 1.72/1.15  Index Insertion      : 0.00
% 1.72/1.15  Index Deletion       : 0.00
% 1.72/1.15  Index Matching       : 0.00
% 1.72/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:22 EST 2020

% Result     : Theorem 2.07s
% Output     : CNFRefutation 2.07s
% Verified   : 
% Statistics : Number of formulae       :   37 (  37 expanded)
%              Number of leaves         :   24 (  24 expanded)
%              Depth                    :    4
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :   14 (  14 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_33,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_46,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_44,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_4,plain,(
    ! [A_3] : k4_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_52,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_55,plain,(
    ! [A_3] : r1_xboole_0(A_3,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_52])).

tff(c_188,plain,(
    ! [A_41,B_42] :
      ( ~ r2_hidden(A_41,B_42)
      | ~ r1_xboole_0(k1_tarski(A_41),B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_196,plain,(
    ! [A_41] : ~ r2_hidden(A_41,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_55,c_188])).

tff(c_38,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_76,plain,(
    ! [A_34,B_35] :
      ( k1_xboole_0 = A_34
      | k2_xboole_0(A_34,B_35) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_80,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_76])).

tff(c_28,plain,(
    ! [A_14] : k2_tarski(A_14,A_14) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_66,plain,(
    ! [D_29,B_30] : r2_hidden(D_29,k2_tarski(D_29,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_69,plain,(
    ! [A_14] : r2_hidden(A_14,k1_tarski(A_14)) ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_66])).

tff(c_85,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_69])).

tff(c_198,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_196,c_85])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 18:15:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.07/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.39  
% 2.07/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.39  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.07/1.39  
% 2.07/1.39  %Foreground sorts:
% 2.07/1.39  
% 2.07/1.39  
% 2.07/1.39  %Background operators:
% 2.07/1.39  
% 2.07/1.39  
% 2.07/1.39  %Foreground operators:
% 2.07/1.39  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.07/1.39  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.07/1.39  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.07/1.39  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.07/1.39  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.07/1.39  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.07/1.39  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.07/1.39  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.07/1.39  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.07/1.39  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.07/1.39  tff('#skF_3', type, '#skF_3': $i).
% 2.07/1.39  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.07/1.39  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.07/1.39  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.07/1.39  tff('#skF_4', type, '#skF_4': $i).
% 2.07/1.39  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.07/1.39  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.07/1.39  
% 2.07/1.40  tff(f_31, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.07/1.40  tff(f_33, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.07/1.40  tff(f_55, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 2.07/1.40  tff(f_61, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.07/1.40  tff(f_29, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t15_xboole_1)).
% 2.07/1.40  tff(f_46, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.07/1.40  tff(f_44, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.07/1.40  tff(c_4, plain, (![A_3]: (k4_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.07/1.40  tff(c_52, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.07/1.40  tff(c_55, plain, (![A_3]: (r1_xboole_0(A_3, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_4, c_52])).
% 2.07/1.40  tff(c_188, plain, (![A_41, B_42]: (~r2_hidden(A_41, B_42) | ~r1_xboole_0(k1_tarski(A_41), B_42))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.07/1.40  tff(c_196, plain, (![A_41]: (~r2_hidden(A_41, k1_xboole_0))), inference(resolution, [status(thm)], [c_55, c_188])).
% 2.07/1.40  tff(c_38, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.07/1.40  tff(c_76, plain, (![A_34, B_35]: (k1_xboole_0=A_34 | k2_xboole_0(A_34, B_35)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.07/1.40  tff(c_80, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_38, c_76])).
% 2.07/1.40  tff(c_28, plain, (![A_14]: (k2_tarski(A_14, A_14)=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.07/1.40  tff(c_66, plain, (![D_29, B_30]: (r2_hidden(D_29, k2_tarski(D_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.07/1.40  tff(c_69, plain, (![A_14]: (r2_hidden(A_14, k1_tarski(A_14)))), inference(superposition, [status(thm), theory('equality')], [c_28, c_66])).
% 2.07/1.40  tff(c_85, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_80, c_69])).
% 2.07/1.40  tff(c_198, plain, $false, inference(negUnitSimplification, [status(thm)], [c_196, c_85])).
% 2.07/1.40  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.07/1.40  
% 2.07/1.40  Inference rules
% 2.07/1.40  ----------------------
% 2.07/1.40  #Ref     : 0
% 2.07/1.40  #Sup     : 41
% 2.07/1.40  #Fact    : 0
% 2.07/1.40  #Define  : 0
% 2.07/1.40  #Split   : 0
% 2.07/1.40  #Chain   : 0
% 2.07/1.40  #Close   : 0
% 2.07/1.40  
% 2.07/1.40  Ordering : KBO
% 2.07/1.40  
% 2.07/1.40  Simplification rules
% 2.07/1.40  ----------------------
% 2.07/1.40  #Subsume      : 0
% 2.07/1.40  #Demod        : 6
% 2.07/1.40  #Tautology    : 30
% 2.07/1.40  #SimpNegUnit  : 1
% 2.07/1.40  #BackRed      : 2
% 2.07/1.40  
% 2.07/1.40  #Partial instantiations: 0
% 2.07/1.40  #Strategies tried      : 1
% 2.07/1.40  
% 2.07/1.40  Timing (in seconds)
% 2.07/1.40  ----------------------
% 2.07/1.40  Preprocessing        : 0.41
% 2.07/1.40  Parsing              : 0.22
% 2.07/1.40  CNF conversion       : 0.02
% 2.07/1.40  Main loop            : 0.15
% 2.07/1.40  Inferencing          : 0.05
% 2.07/1.40  Reduction            : 0.05
% 2.07/1.41  Demodulation         : 0.04
% 2.07/1.41  BG Simplification    : 0.01
% 2.07/1.41  Subsumption          : 0.03
% 2.07/1.41  Abstraction          : 0.01
% 2.07/1.41  MUC search           : 0.00
% 2.07/1.41  Cooper               : 0.00
% 2.07/1.41  Total                : 0.58
% 2.07/1.41  Index Insertion      : 0.00
% 2.07/1.41  Index Deletion       : 0.00
% 2.07/1.41  Index Matching       : 0.00
% 2.07/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------

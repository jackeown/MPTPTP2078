%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:57:35 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.27s
% Verified   : 
% Statistics : Number of formulae       :   41 (  42 expanded)
%              Number of leaves         :   28 (  29 expanded)
%              Depth                    :    7
%              Number of atoms          :   34 (  36 expanded)
%              Number of equality atoms :    8 (   9 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r1_setfam_1,type,(
    r1_setfam_1: ( $i * $i ) > $o )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(k1_setfam_1,type,(
    k1_setfam_1: $i > $i )).

tff(f_82,negated_conjecture,(
    ~ ! [A] :
        ( r1_setfam_1(A,k1_xboole_0)
       => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_setfam_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_75,axiom,(
    ! [A,B] :
      ( r1_setfam_1(A,B)
    <=> ! [C] :
          ~ ( r2_hidden(C,A)
            & ! [D] :
                ~ ( r2_hidden(D,B)
                  & r1_tarski(C,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_setfam_1)).

tff(f_51,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(c_34,plain,(
    k1_xboole_0 != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_36,plain,(
    r1_setfam_1('#skF_5',k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_221,plain,(
    ! [A_94,B_95,C_96] :
      ( r2_hidden('#skF_4'(A_94,B_95,C_96),B_95)
      | ~ r2_hidden(C_96,A_94)
      | ~ r1_setfam_1(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_10,plain,(
    ! [A_10] : r1_xboole_0(A_10,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_66,plain,(
    ! [A_59,B_60,C_61] :
      ( ~ r1_xboole_0(A_59,B_60)
      | ~ r2_hidden(C_61,k3_xboole_0(A_59,B_60)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_75,plain,(
    ! [A_62,C_63] :
      ( ~ r1_xboole_0(A_62,A_62)
      | ~ r2_hidden(C_63,A_62) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_66])).

tff(c_79,plain,(
    ! [C_63] : ~ r2_hidden(C_63,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_10,c_75])).

tff(c_232,plain,(
    ! [C_97,A_98] :
      ( ~ r2_hidden(C_97,A_98)
      | ~ r1_setfam_1(A_98,k1_xboole_0) ) ),
    inference(resolution,[status(thm)],[c_221,c_79])).

tff(c_262,plain,(
    ! [A_104] :
      ( ~ r1_setfam_1(A_104,k1_xboole_0)
      | k1_xboole_0 = A_104 ) ),
    inference(resolution,[status(thm)],[c_8,c_232])).

tff(c_273,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(resolution,[status(thm)],[c_36,c_262])).

tff(c_280,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_273])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n015.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 15:07:08 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.23  
% 2.09/1.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.09/1.23  %$ r2_hidden > r1_xboole_0 > r1_tarski > r1_setfam_1 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_setfam_1 > k1_xboole_0 > #skF_2 > #skF_4 > #skF_3 > #skF_5 > #skF_1
% 2.09/1.23  
% 2.09/1.23  %Foreground sorts:
% 2.09/1.23  
% 2.09/1.23  
% 2.09/1.23  %Background operators:
% 2.09/1.23  
% 2.09/1.23  
% 2.09/1.23  %Foreground operators:
% 2.09/1.23  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.09/1.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.23  tff(r1_setfam_1, type, r1_setfam_1: ($i * $i) > $o).
% 2.09/1.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.09/1.23  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.09/1.23  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.09/1.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.23  tff('#skF_5', type, '#skF_5': $i).
% 2.09/1.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.23  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.09/1.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.23  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.09/1.23  tff(k1_setfam_1, type, k1_setfam_1: $i > $i).
% 2.09/1.23  
% 2.27/1.24  tff(f_82, negated_conjecture, ~(![A]: (r1_setfam_1(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_setfam_1)).
% 2.27/1.24  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.27/1.24  tff(f_75, axiom, (![A, B]: (r1_setfam_1(A, B) <=> (![C]: ~(r2_hidden(C, A) & (![D]: ~(r2_hidden(D, B) & r1_tarski(C, D))))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_setfam_1)).
% 2.27/1.24  tff(f_51, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.27/1.24  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.27/1.24  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.27/1.24  tff(c_34, plain, (k1_xboole_0!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.27/1.24  tff(c_36, plain, (r1_setfam_1('#skF_5', k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_82])).
% 2.27/1.24  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.27/1.24  tff(c_221, plain, (![A_94, B_95, C_96]: (r2_hidden('#skF_4'(A_94, B_95, C_96), B_95) | ~r2_hidden(C_96, A_94) | ~r1_setfam_1(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_75])).
% 2.27/1.24  tff(c_10, plain, (![A_10]: (r1_xboole_0(A_10, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.27/1.24  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.27/1.24  tff(c_66, plain, (![A_59, B_60, C_61]: (~r1_xboole_0(A_59, B_60) | ~r2_hidden(C_61, k3_xboole_0(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.27/1.24  tff(c_75, plain, (![A_62, C_63]: (~r1_xboole_0(A_62, A_62) | ~r2_hidden(C_63, A_62))), inference(superposition, [status(thm), theory('equality')], [c_2, c_66])).
% 2.27/1.24  tff(c_79, plain, (![C_63]: (~r2_hidden(C_63, k1_xboole_0))), inference(resolution, [status(thm)], [c_10, c_75])).
% 2.27/1.24  tff(c_232, plain, (![C_97, A_98]: (~r2_hidden(C_97, A_98) | ~r1_setfam_1(A_98, k1_xboole_0))), inference(resolution, [status(thm)], [c_221, c_79])).
% 2.27/1.24  tff(c_262, plain, (![A_104]: (~r1_setfam_1(A_104, k1_xboole_0) | k1_xboole_0=A_104)), inference(resolution, [status(thm)], [c_8, c_232])).
% 2.27/1.24  tff(c_273, plain, (k1_xboole_0='#skF_5'), inference(resolution, [status(thm)], [c_36, c_262])).
% 2.27/1.24  tff(c_280, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_273])).
% 2.27/1.24  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.27/1.24  
% 2.27/1.24  Inference rules
% 2.27/1.24  ----------------------
% 2.27/1.24  #Ref     : 0
% 2.27/1.24  #Sup     : 50
% 2.27/1.24  #Fact    : 0
% 2.27/1.24  #Define  : 0
% 2.27/1.24  #Split   : 0
% 2.27/1.24  #Chain   : 0
% 2.27/1.24  #Close   : 0
% 2.27/1.24  
% 2.27/1.24  Ordering : KBO
% 2.27/1.24  
% 2.27/1.24  Simplification rules
% 2.27/1.24  ----------------------
% 2.27/1.24  #Subsume      : 5
% 2.27/1.24  #Demod        : 14
% 2.27/1.24  #Tautology    : 27
% 2.27/1.24  #SimpNegUnit  : 2
% 2.27/1.24  #BackRed      : 0
% 2.27/1.24  
% 2.27/1.24  #Partial instantiations: 0
% 2.27/1.24  #Strategies tried      : 1
% 2.27/1.24  
% 2.27/1.24  Timing (in seconds)
% 2.27/1.24  ----------------------
% 2.27/1.24  Preprocessing        : 0.31
% 2.27/1.24  Parsing              : 0.17
% 2.27/1.24  CNF conversion       : 0.02
% 2.27/1.24  Main loop            : 0.17
% 2.27/1.24  Inferencing          : 0.07
% 2.27/1.24  Reduction            : 0.05
% 2.27/1.24  Demodulation         : 0.03
% 2.27/1.24  BG Simplification    : 0.01
% 2.27/1.24  Subsumption          : 0.02
% 2.27/1.24  Abstraction          : 0.01
% 2.27/1.24  MUC search           : 0.00
% 2.27/1.24  Cooper               : 0.00
% 2.27/1.24  Total                : 0.50
% 2.27/1.24  Index Insertion      : 0.00
% 2.27/1.24  Index Deletion       : 0.00
% 2.27/1.24  Index Matching       : 0.00
% 2.27/1.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------

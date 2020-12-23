%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:22 EST 2020

% Result     : Theorem 2.39s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   43 (  44 expanded)
%              Number of leaves         :   28 (  29 expanded)
%              Depth                    :    5
%              Number of atoms          :   34 (  36 expanded)
%              Number of equality atoms :   17 (  18 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3

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

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_32,axiom,(
    k1_xboole_0 = o_0_0_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_xboole_0)).

tff(f_33,axiom,(
    v1_xboole_0(o_0_0_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',dt_o_0_0_xboole_0)).

tff(f_90,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),k1_tarski(C))
       => k2_tarski(A,B) = k1_tarski(C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t27_zfmisc_1)).

tff(f_85,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_6,plain,(
    o_0_0_xboole_0 = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    v1_xboole_0(o_0_0_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_59,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_8])).

tff(c_56,plain,(
    k2_tarski('#skF_5','#skF_6') != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_58,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k1_tarski('#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_174,plain,(
    ! [B_72,A_73] :
      ( k1_tarski(B_72) = A_73
      | k1_xboole_0 = A_73
      | ~ r1_tarski(A_73,k1_tarski(B_72)) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_177,plain,
    ( k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7')
    | k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_58,c_174])).

tff(c_186,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_177])).

tff(c_97,plain,(
    ! [A_49,B_50] : k1_enumset1(A_49,A_49,B_50) = k2_tarski(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_76,plain,(
    ! [E_36,B_37,C_38] : r2_hidden(E_36,k1_enumset1(E_36,B_37,C_38)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,(
    ! [E_36,B_37,C_38] : ~ v1_xboole_0(k1_enumset1(E_36,B_37,C_38)) ),
    inference(resolution,[status(thm)],[c_76,c_2])).

tff(c_108,plain,(
    ! [A_49,B_50] : ~ v1_xboole_0(k2_tarski(A_49,B_50)) ),
    inference(superposition,[status(thm),theory(equality)],[c_97,c_80])).

tff(c_202,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_186,c_108])).

tff(c_207,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_59,c_202])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.35  % Computer   : n025.cluster.edu
% 0.15/0.35  % Model      : x86_64 x86_64
% 0.15/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.35  % Memory     : 8042.1875MB
% 0.15/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.35  % CPULimit   : 60
% 0.15/0.35  % DateTime   : Tue Dec  1 19:48:51 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.39/1.39  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.39  
% 2.39/1.39  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.40  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > o_0_0_xboole_0 > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_2 > #skF_3
% 2.39/1.40  
% 2.39/1.40  %Foreground sorts:
% 2.39/1.40  
% 2.39/1.40  
% 2.39/1.40  %Background operators:
% 2.39/1.40  
% 2.39/1.40  
% 2.39/1.40  %Foreground operators:
% 2.39/1.40  tff(o_0_0_xboole_0, type, o_0_0_xboole_0: $i).
% 2.39/1.40  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.40  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.40  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.39/1.40  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.39/1.40  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.40  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.39/1.40  tff('#skF_7', type, '#skF_7': $i).
% 2.39/1.40  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.40  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.39/1.40  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.39/1.40  tff('#skF_5', type, '#skF_5': $i).
% 2.39/1.40  tff('#skF_6', type, '#skF_6': $i).
% 2.39/1.40  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.39/1.40  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.39/1.40  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.39/1.40  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.40  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.40  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.39/1.40  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.39/1.40  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.39/1.40  
% 2.39/1.41  tff(f_32, axiom, (k1_xboole_0 = o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_xboole_0)).
% 2.39/1.41  tff(f_33, axiom, v1_xboole_0(o_0_0_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', dt_o_0_0_xboole_0)).
% 2.39/1.41  tff(f_90, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), k1_tarski(C)) => (k2_tarski(A, B) = k1_tarski(C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t27_zfmisc_1)).
% 2.39/1.41  tff(f_85, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 2.39/1.41  tff(f_70, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.39/1.41  tff(f_66, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.39/1.41  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.39/1.41  tff(c_6, plain, (o_0_0_xboole_0=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_32])).
% 2.39/1.41  tff(c_8, plain, (v1_xboole_0(o_0_0_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.39/1.41  tff(c_59, plain, (v1_xboole_0(k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_8])).
% 2.39/1.41  tff(c_56, plain, (k2_tarski('#skF_5', '#skF_6')!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.39/1.41  tff(c_58, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k1_tarski('#skF_7'))), inference(cnfTransformation, [status(thm)], [f_90])).
% 2.39/1.41  tff(c_174, plain, (![B_72, A_73]: (k1_tarski(B_72)=A_73 | k1_xboole_0=A_73 | ~r1_tarski(A_73, k1_tarski(B_72)))), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.39/1.41  tff(c_177, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7') | k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_58, c_174])).
% 2.39/1.41  tff(c_186, plain, (k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(negUnitSimplification, [status(thm)], [c_56, c_177])).
% 2.39/1.41  tff(c_97, plain, (![A_49, B_50]: (k1_enumset1(A_49, A_49, B_50)=k2_tarski(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_70])).
% 2.39/1.41  tff(c_76, plain, (![E_36, B_37, C_38]: (r2_hidden(E_36, k1_enumset1(E_36, B_37, C_38)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 2.39/1.41  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.39/1.41  tff(c_80, plain, (![E_36, B_37, C_38]: (~v1_xboole_0(k1_enumset1(E_36, B_37, C_38)))), inference(resolution, [status(thm)], [c_76, c_2])).
% 2.39/1.41  tff(c_108, plain, (![A_49, B_50]: (~v1_xboole_0(k2_tarski(A_49, B_50)))), inference(superposition, [status(thm), theory('equality')], [c_97, c_80])).
% 2.39/1.41  tff(c_202, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_186, c_108])).
% 2.39/1.41  tff(c_207, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_59, c_202])).
% 2.39/1.41  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.41  
% 2.39/1.41  Inference rules
% 2.39/1.41  ----------------------
% 2.39/1.41  #Ref     : 0
% 2.39/1.41  #Sup     : 34
% 2.39/1.41  #Fact    : 0
% 2.39/1.41  #Define  : 0
% 2.39/1.41  #Split   : 0
% 2.39/1.41  #Chain   : 0
% 2.39/1.41  #Close   : 0
% 2.39/1.41  
% 2.39/1.41  Ordering : KBO
% 2.39/1.41  
% 2.39/1.41  Simplification rules
% 2.39/1.41  ----------------------
% 2.39/1.41  #Subsume      : 9
% 2.39/1.41  #Demod        : 7
% 2.39/1.41  #Tautology    : 13
% 2.39/1.41  #SimpNegUnit  : 1
% 2.39/1.41  #BackRed      : 2
% 2.39/1.41  
% 2.39/1.41  #Partial instantiations: 0
% 2.39/1.41  #Strategies tried      : 1
% 2.39/1.41  
% 2.39/1.41  Timing (in seconds)
% 2.39/1.41  ----------------------
% 2.39/1.41  Preprocessing        : 0.42
% 2.39/1.41  Parsing              : 0.21
% 2.39/1.41  CNF conversion       : 0.03
% 2.39/1.41  Main loop            : 0.17
% 2.39/1.41  Inferencing          : 0.05
% 2.39/1.41  Reduction            : 0.06
% 2.39/1.41  Demodulation         : 0.04
% 2.39/1.41  BG Simplification    : 0.02
% 2.39/1.41  Subsumption          : 0.04
% 2.39/1.41  Abstraction          : 0.01
% 2.39/1.41  MUC search           : 0.00
% 2.39/1.41  Cooper               : 0.00
% 2.39/1.41  Total                : 0.62
% 2.39/1.41  Index Insertion      : 0.00
% 2.39/1.41  Index Deletion       : 0.00
% 2.39/1.41  Index Matching       : 0.00
% 2.39/1.41  BG Taut test         : 0.00
%------------------------------------------------------------------------------

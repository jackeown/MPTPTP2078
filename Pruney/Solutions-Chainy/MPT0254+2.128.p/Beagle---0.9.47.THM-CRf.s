%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:35 EST 2020

% Result     : Theorem 2.12s
% Output     : CNFRefutation 2.12s
% Verified   : 
% Statistics : Number of formulae       :   43 (  43 expanded)
%              Number of leaves         :   30 (  30 expanded)
%              Depth                    :    5
%              Number of atoms          :   25 (  25 expanded)
%              Number of equality atoms :   13 (  13 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_39,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_95,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_55,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_78,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_12,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_66,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_95])).

tff(c_137,plain,(
    ! [A_65,B_66] : k4_xboole_0(A_65,k2_xboole_0(A_65,B_66)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_144,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_66,c_137])).

tff(c_22,plain,(
    ! [A_16] : k4_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_150,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_22])).

tff(c_54,plain,(
    ! [A_33] : k2_tarski(A_33,A_33) = k1_tarski(A_33) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_99,plain,(
    ! [D_52,A_53] : r2_hidden(D_52,k2_tarski(A_53,D_52)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_2,plain,(
    ! [B_4,A_1] :
      ( ~ r2_hidden(B_4,A_1)
      | ~ v1_xboole_0(A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_107,plain,(
    ! [A_54,D_55] : ~ v1_xboole_0(k2_tarski(A_54,D_55)) ),
    inference(resolution,[status(thm)],[c_99,c_2])).

tff(c_109,plain,(
    ! [A_33] : ~ v1_xboole_0(k1_tarski(A_33)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_107])).

tff(c_165,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_109])).

tff(c_170,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_165])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:39:17 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.12/1.21  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.21  
% 2.12/1.21  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.22  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_5 > #skF_6 > #skF_3 > #skF_2
% 2.12/1.22  
% 2.12/1.22  %Foreground sorts:
% 2.12/1.22  
% 2.12/1.22  
% 2.12/1.22  %Background operators:
% 2.12/1.22  
% 2.12/1.22  
% 2.12/1.22  %Foreground operators:
% 2.12/1.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.12/1.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.12/1.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.12/1.22  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.12/1.22  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.12/1.22  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.12/1.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.12/1.22  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.12/1.22  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.12/1.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.12/1.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.12/1.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.12/1.22  tff('#skF_5', type, '#skF_5': $i).
% 2.12/1.22  tff('#skF_6', type, '#skF_6': $i).
% 2.12/1.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.12/1.22  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.12/1.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.12/1.22  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.12/1.22  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.12/1.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.12/1.22  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 2.12/1.22  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.12/1.22  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.12/1.22  
% 2.12/1.22  tff(f_39, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.12/1.22  tff(f_95, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.12/1.22  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 2.12/1.22  tff(f_55, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 2.12/1.22  tff(f_78, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.12/1.22  tff(f_76, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.12/1.22  tff(f_31, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.12/1.22  tff(c_12, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.12/1.22  tff(c_66, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_95])).
% 2.12/1.22  tff(c_137, plain, (![A_65, B_66]: (k4_xboole_0(A_65, k2_xboole_0(A_65, B_66))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.12/1.22  tff(c_144, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_xboole_0)=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_66, c_137])).
% 2.12/1.22  tff(c_22, plain, (![A_16]: (k4_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.12/1.22  tff(c_150, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_144, c_22])).
% 2.12/1.22  tff(c_54, plain, (![A_33]: (k2_tarski(A_33, A_33)=k1_tarski(A_33))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.12/1.22  tff(c_99, plain, (![D_52, A_53]: (r2_hidden(D_52, k2_tarski(A_53, D_52)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 2.12/1.22  tff(c_2, plain, (![B_4, A_1]: (~r2_hidden(B_4, A_1) | ~v1_xboole_0(A_1))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.12/1.22  tff(c_107, plain, (![A_54, D_55]: (~v1_xboole_0(k2_tarski(A_54, D_55)))), inference(resolution, [status(thm)], [c_99, c_2])).
% 2.12/1.22  tff(c_109, plain, (![A_33]: (~v1_xboole_0(k1_tarski(A_33)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_107])).
% 2.12/1.22  tff(c_165, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_150, c_109])).
% 2.12/1.22  tff(c_170, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_12, c_165])).
% 2.12/1.22  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.12/1.22  
% 2.12/1.22  Inference rules
% 2.12/1.22  ----------------------
% 2.12/1.22  #Ref     : 0
% 2.12/1.23  #Sup     : 27
% 2.12/1.23  #Fact    : 0
% 2.12/1.23  #Define  : 0
% 2.12/1.23  #Split   : 0
% 2.12/1.23  #Chain   : 0
% 2.12/1.23  #Close   : 0
% 2.12/1.23  
% 2.12/1.23  Ordering : KBO
% 2.12/1.23  
% 2.12/1.23  Simplification rules
% 2.12/1.23  ----------------------
% 2.12/1.23  #Subsume      : 2
% 2.12/1.23  #Demod        : 6
% 2.12/1.23  #Tautology    : 16
% 2.12/1.23  #SimpNegUnit  : 0
% 2.12/1.23  #BackRed      : 2
% 2.12/1.23  
% 2.12/1.23  #Partial instantiations: 0
% 2.12/1.23  #Strategies tried      : 1
% 2.12/1.23  
% 2.12/1.23  Timing (in seconds)
% 2.12/1.23  ----------------------
% 2.12/1.23  Preprocessing        : 0.33
% 2.12/1.23  Parsing              : 0.17
% 2.12/1.23  CNF conversion       : 0.02
% 2.12/1.23  Main loop            : 0.13
% 2.12/1.23  Inferencing          : 0.04
% 2.12/1.23  Reduction            : 0.05
% 2.12/1.23  Demodulation         : 0.04
% 2.12/1.23  BG Simplification    : 0.01
% 2.12/1.23  Subsumption          : 0.02
% 2.12/1.23  Abstraction          : 0.01
% 2.12/1.23  MUC search           : 0.00
% 2.12/1.23  Cooper               : 0.00
% 2.12/1.23  Total                : 0.48
% 2.12/1.23  Index Insertion      : 0.00
% 2.12/1.23  Index Deletion       : 0.00
% 2.12/1.23  Index Matching       : 0.00
% 2.18/1.23  BG Taut test         : 0.00
%------------------------------------------------------------------------------

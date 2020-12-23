%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:26 EST 2020

% Result     : Theorem 1.80s
% Output     : CNFRefutation 1.90s
% Verified   : 
% Statistics : Number of formulae       :   38 (  38 expanded)
%              Number of leaves         :   25 (  25 expanded)
%              Depth                    :    5
%              Number of atoms          :   27 (  27 expanded)
%              Number of equality atoms :   10 (  10 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_34,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_40,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_38,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_33,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
    <=> ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_xboole_0)).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_73,plain,(
    ! [A_34,B_35] : r1_tarski(A_34,k2_xboole_0(A_34,B_35)) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_76,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_73])).

tff(c_10,plain,(
    ! [A_7] :
      ( k1_xboole_0 = A_7
      | ~ r1_tarski(A_7,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_80,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_76,c_10])).

tff(c_32,plain,(
    ! [A_16] : k2_tarski(A_16,A_16) = k1_tarski(A_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_56,plain,(
    ! [D_28,B_29] : r2_hidden(D_28,k2_tarski(D_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_64,plain,(
    ! [D_30,B_31] : ~ v1_xboole_0(k2_tarski(D_30,B_31)) ),
    inference(resolution,[status(thm)],[c_56,c_4])).

tff(c_66,plain,(
    ! [A_16] : ~ v1_xboole_0(k1_tarski(A_16)) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_64])).

tff(c_88,plain,(
    ~ v1_xboole_0(k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_80,c_66])).

tff(c_93,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_88])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 16:15:04 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.80/1.19  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.80/1.19  
% 1.80/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.20  %$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 1.90/1.20  
% 1.90/1.20  %Foreground sorts:
% 1.90/1.20  
% 1.90/1.20  
% 1.90/1.20  %Background operators:
% 1.90/1.20  
% 1.90/1.20  
% 1.90/1.20  %Foreground operators:
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.90/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.90/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.90/1.20  tff('#skF_1', type, '#skF_1': $i > $i).
% 1.90/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.90/1.20  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.90/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.90/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.90/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.90/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.90/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.90/1.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.90/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.90/1.20  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 1.90/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.90/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.90/1.20  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 1.90/1.20  
% 1.90/1.21  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 1.90/1.21  tff(f_61, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.90/1.21  tff(f_40, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 1.90/1.21  tff(f_38, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 1.90/1.21  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 1.90/1.21  tff(f_49, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 1.90/1.21  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 1.90/1.21  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 1.90/1.21  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 1.90/1.21  tff(c_73, plain, (![A_34, B_35]: (r1_tarski(A_34, k2_xboole_0(A_34, B_35)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.90/1.21  tff(c_76, plain, (r1_tarski(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_40, c_73])).
% 1.90/1.21  tff(c_10, plain, (![A_7]: (k1_xboole_0=A_7 | ~r1_tarski(A_7, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.90/1.21  tff(c_80, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(resolution, [status(thm)], [c_76, c_10])).
% 1.90/1.21  tff(c_32, plain, (![A_16]: (k2_tarski(A_16, A_16)=k1_tarski(A_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 1.90/1.21  tff(c_56, plain, (![D_28, B_29]: (r2_hidden(D_28, k2_tarski(D_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.90/1.21  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.90/1.21  tff(c_64, plain, (![D_30, B_31]: (~v1_xboole_0(k2_tarski(D_30, B_31)))), inference(resolution, [status(thm)], [c_56, c_4])).
% 1.90/1.21  tff(c_66, plain, (![A_16]: (~v1_xboole_0(k1_tarski(A_16)))), inference(superposition, [status(thm), theory('equality')], [c_32, c_64])).
% 1.90/1.21  tff(c_88, plain, (~v1_xboole_0(k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_80, c_66])).
% 1.90/1.21  tff(c_93, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_88])).
% 1.90/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 1.90/1.21  
% 1.90/1.21  Inference rules
% 1.90/1.21  ----------------------
% 1.90/1.21  #Ref     : 0
% 1.90/1.21  #Sup     : 14
% 1.90/1.21  #Fact    : 0
% 1.90/1.21  #Define  : 0
% 1.90/1.21  #Split   : 0
% 1.90/1.21  #Chain   : 0
% 1.90/1.21  #Close   : 0
% 1.90/1.21  
% 1.90/1.21  Ordering : KBO
% 1.90/1.21  
% 1.90/1.21  Simplification rules
% 1.90/1.21  ----------------------
% 1.90/1.21  #Subsume      : 1
% 1.90/1.21  #Demod        : 3
% 1.90/1.21  #Tautology    : 5
% 1.90/1.21  #SimpNegUnit  : 0
% 1.90/1.21  #BackRed      : 2
% 1.90/1.21  
% 1.90/1.21  #Partial instantiations: 0
% 1.90/1.21  #Strategies tried      : 1
% 1.90/1.21  
% 1.90/1.21  Timing (in seconds)
% 1.90/1.21  ----------------------
% 1.90/1.21  Preprocessing        : 0.29
% 1.90/1.21  Parsing              : 0.15
% 1.90/1.21  CNF conversion       : 0.02
% 1.90/1.21  Main loop            : 0.10
% 1.90/1.21  Inferencing          : 0.03
% 1.90/1.21  Reduction            : 0.04
% 1.90/1.21  Demodulation         : 0.03
% 1.90/1.21  BG Simplification    : 0.01
% 1.90/1.21  Subsumption          : 0.02
% 1.90/1.21  Abstraction          : 0.01
% 1.90/1.21  MUC search           : 0.00
% 1.90/1.21  Cooper               : 0.00
% 1.90/1.21  Total                : 0.42
% 1.90/1.21  Index Insertion      : 0.00
% 1.90/1.21  Index Deletion       : 0.00
% 1.90/1.21  Index Matching       : 0.00
% 1.90/1.21  BG Taut test         : 0.00
%------------------------------------------------------------------------------

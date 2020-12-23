%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:22 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   34 (  34 expanded)
%              Number of leaves         :   23 (  23 expanded)
%              Depth                    :    4
%              Number of atoms          :   24 (  24 expanded)
%              Number of equality atoms :   12 (  12 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(f_37,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_50,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_8,plain,(
    ! [A_6] : r1_xboole_0(A_6,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_137,plain,(
    ! [A_37,B_38] :
      ( ~ r2_hidden(A_37,B_38)
      | ~ r1_xboole_0(k1_tarski(A_37),B_38) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_145,plain,(
    ! [A_37] : ~ r2_hidden(A_37,k1_xboole_0) ),
    inference(resolution,[status(thm)],[c_8,c_137])).

tff(c_40,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_66,plain,(
    ! [A_33,B_34] :
      ( k1_xboole_0 = A_33
      | k2_xboole_0(A_33,B_34) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_70,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_66])).

tff(c_30,plain,(
    ! [A_15] : k2_tarski(A_15,A_15) = k1_tarski(A_15) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_56,plain,(
    ! [D_28,B_29] : r2_hidden(D_28,k2_tarski(D_28,B_29)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_59,plain,(
    ! [A_15] : r2_hidden(A_15,k1_tarski(A_15)) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_56])).

tff(c_75,plain,(
    r2_hidden('#skF_3',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_59])).

tff(c_147,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_145,c_75])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:03:52 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.18  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.19  
% 1.92/1.19  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.19  %$ r2_hidden > r1_xboole_0 > r1_tarski > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.92/1.19  
% 1.92/1.19  %Foreground sorts:
% 1.92/1.19  
% 1.92/1.19  
% 1.92/1.19  %Background operators:
% 1.92/1.19  
% 1.92/1.19  
% 1.92/1.19  %Foreground operators:
% 1.92/1.19  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.92/1.19  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.19  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.19  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.92/1.19  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.19  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.92/1.19  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.92/1.19  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.19  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.92/1.19  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.92/1.19  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.19  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.92/1.19  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.19  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.92/1.19  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.19  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.19  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.92/1.19  
% 1.92/1.20  tff(f_37, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.92/1.20  tff(f_59, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.92/1.20  tff(f_65, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.92/1.20  tff(f_33, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 1.92/1.20  tff(f_50, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.92/1.20  tff(f_48, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.92/1.20  tff(c_8, plain, (![A_6]: (r1_xboole_0(A_6, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.92/1.20  tff(c_137, plain, (![A_37, B_38]: (~r2_hidden(A_37, B_38) | ~r1_xboole_0(k1_tarski(A_37), B_38))), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.92/1.20  tff(c_145, plain, (![A_37]: (~r2_hidden(A_37, k1_xboole_0))), inference(resolution, [status(thm)], [c_8, c_137])).
% 1.92/1.20  tff(c_40, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 1.92/1.20  tff(c_66, plain, (![A_33, B_34]: (k1_xboole_0=A_33 | k2_xboole_0(A_33, B_34)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.20  tff(c_70, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_40, c_66])).
% 1.92/1.20  tff(c_30, plain, (![A_15]: (k2_tarski(A_15, A_15)=k1_tarski(A_15))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.92/1.20  tff(c_56, plain, (![D_28, B_29]: (r2_hidden(D_28, k2_tarski(D_28, B_29)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.92/1.20  tff(c_59, plain, (![A_15]: (r2_hidden(A_15, k1_tarski(A_15)))), inference(superposition, [status(thm), theory('equality')], [c_30, c_56])).
% 1.92/1.20  tff(c_75, plain, (r2_hidden('#skF_3', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_70, c_59])).
% 1.92/1.20  tff(c_147, plain, $false, inference(negUnitSimplification, [status(thm)], [c_145, c_75])).
% 1.92/1.20  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.20  
% 1.92/1.20  Inference rules
% 1.92/1.20  ----------------------
% 1.92/1.20  #Ref     : 0
% 1.92/1.20  #Sup     : 27
% 1.92/1.20  #Fact    : 0
% 1.92/1.20  #Define  : 0
% 1.92/1.20  #Split   : 0
% 1.92/1.20  #Chain   : 0
% 1.92/1.20  #Close   : 0
% 1.92/1.20  
% 1.92/1.20  Ordering : KBO
% 1.92/1.20  
% 1.92/1.20  Simplification rules
% 1.92/1.20  ----------------------
% 1.92/1.20  #Subsume      : 0
% 1.92/1.20  #Demod        : 6
% 1.92/1.20  #Tautology    : 22
% 1.92/1.20  #SimpNegUnit  : 1
% 1.92/1.20  #BackRed      : 2
% 1.92/1.20  
% 1.92/1.20  #Partial instantiations: 0
% 1.92/1.20  #Strategies tried      : 1
% 1.92/1.20  
% 1.92/1.20  Timing (in seconds)
% 1.92/1.20  ----------------------
% 1.92/1.20  Preprocessing        : 0.32
% 1.92/1.20  Parsing              : 0.16
% 1.92/1.20  CNF conversion       : 0.02
% 1.92/1.20  Main loop            : 0.12
% 1.92/1.20  Inferencing          : 0.04
% 1.92/1.20  Reduction            : 0.05
% 1.92/1.20  Demodulation         : 0.04
% 1.92/1.20  BG Simplification    : 0.01
% 1.92/1.20  Subsumption          : 0.02
% 1.92/1.20  Abstraction          : 0.01
% 1.92/1.20  MUC search           : 0.00
% 1.92/1.20  Cooper               : 0.00
% 1.92/1.20  Total                : 0.47
% 1.92/1.20  Index Insertion      : 0.00
% 1.92/1.20  Index Deletion       : 0.00
% 1.92/1.20  Index Matching       : 0.00
% 1.92/1.20  BG Taut test         : 0.00
%------------------------------------------------------------------------------

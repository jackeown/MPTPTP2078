%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:43 EST 2020

% Result     : Theorem 2.29s
% Output     : CNFRefutation 2.39s
% Verified   : 
% Statistics : Number of formulae       :   47 (  69 expanded)
%              Number of leaves         :   27 (  36 expanded)
%              Depth                    :    8
%              Number of atoms          :   39 (  70 expanded)
%              Number of equality atoms :   14 (  26 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_1',type,(
    '#skF_1': $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(f_42,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_65,negated_conjecture,(
    ~ ! [A,B,C] : k2_xboole_0(k2_tarski(A,B),C) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_44,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_34,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_53,axiom,(
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

tff(c_16,plain,(
    ! [A_9] : r1_tarski(k1_xboole_0,A_9) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_46,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_75,plain,(
    ! [B_42,A_43] : k2_xboole_0(B_42,A_43) = k2_xboole_0(A_43,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_126,plain,(
    ! [A_44,B_45] : r1_tarski(A_44,k2_xboole_0(B_45,A_44)) ),
    inference(superposition,[status(thm),theory(equality)],[c_75,c_18])).

tff(c_135,plain,(
    r1_tarski('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_126])).

tff(c_172,plain,(
    ! [B_50,A_51] :
      ( B_50 = A_51
      | ~ r1_tarski(B_50,A_51)
      | ~ r1_tarski(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_174,plain,
    ( k1_xboole_0 = '#skF_6'
    | ~ r1_tarski(k1_xboole_0,'#skF_6') ),
    inference(resolution,[status(thm)],[c_135,c_172])).

tff(c_187,plain,(
    k1_xboole_0 = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_174])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_203,plain,(
    v1_xboole_0('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_8])).

tff(c_66,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_46,c_18])).

tff(c_178,plain,
    ( k2_tarski('#skF_4','#skF_5') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k2_tarski('#skF_4','#skF_5')) ),
    inference(resolution,[status(thm)],[c_66,c_172])).

tff(c_191,plain,(
    k2_tarski('#skF_4','#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_178])).

tff(c_222,plain,(
    k2_tarski('#skF_4','#skF_5') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_187,c_191])).

tff(c_24,plain,(
    ! [D_17,B_13] : r2_hidden(D_17,k2_tarski(D_17,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_51,plain,(
    ! [B_33,A_34] :
      ( ~ r2_hidden(B_33,A_34)
      | ~ v1_xboole_0(A_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_55,plain,(
    ! [D_17,B_13] : ~ v1_xboole_0(k2_tarski(D_17,B_13)) ),
    inference(resolution,[status(thm)],[c_24,c_51])).

tff(c_228,plain,(
    ~ v1_xboole_0('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_222,c_55])).

tff(c_239,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_203,c_228])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:06:07 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.29/1.57  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.58  
% 2.39/1.58  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.58  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 2.39/1.58  
% 2.39/1.58  %Foreground sorts:
% 2.39/1.58  
% 2.39/1.58  
% 2.39/1.58  %Background operators:
% 2.39/1.58  
% 2.39/1.58  
% 2.39/1.58  %Foreground operators:
% 2.39/1.58  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.39/1.58  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.39/1.58  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.39/1.58  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.39/1.58  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.39/1.58  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.39/1.58  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.39/1.58  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.39/1.58  tff('#skF_5', type, '#skF_5': $i).
% 2.39/1.58  tff('#skF_6', type, '#skF_6': $i).
% 2.39/1.58  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.39/1.58  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.39/1.58  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.39/1.58  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.39/1.58  tff('#skF_4', type, '#skF_4': $i).
% 2.39/1.58  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.39/1.58  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.39/1.58  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.39/1.58  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.39/1.58  
% 2.39/1.60  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.39/1.60  tff(f_65, negated_conjecture, ~(![A, B, C]: ~(k2_xboole_0(k2_tarski(A, B), C) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_zfmisc_1)).
% 2.39/1.60  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.39/1.60  tff(f_44, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.39/1.60  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.39/1.60  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.39/1.60  tff(f_53, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.39/1.60  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.39/1.60  tff(c_16, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.39/1.60  tff(c_46, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_65])).
% 2.39/1.60  tff(c_75, plain, (![B_42, A_43]: (k2_xboole_0(B_42, A_43)=k2_xboole_0(A_43, B_42))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.39/1.60  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.39/1.60  tff(c_126, plain, (![A_44, B_45]: (r1_tarski(A_44, k2_xboole_0(B_45, A_44)))), inference(superposition, [status(thm), theory('equality')], [c_75, c_18])).
% 2.39/1.60  tff(c_135, plain, (r1_tarski('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_126])).
% 2.39/1.60  tff(c_172, plain, (![B_50, A_51]: (B_50=A_51 | ~r1_tarski(B_50, A_51) | ~r1_tarski(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.39/1.60  tff(c_174, plain, (k1_xboole_0='#skF_6' | ~r1_tarski(k1_xboole_0, '#skF_6')), inference(resolution, [status(thm)], [c_135, c_172])).
% 2.39/1.60  tff(c_187, plain, (k1_xboole_0='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_174])).
% 2.39/1.60  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.39/1.60  tff(c_203, plain, (v1_xboole_0('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_187, c_8])).
% 2.39/1.60  tff(c_66, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_46, c_18])).
% 2.39/1.60  tff(c_178, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k2_tarski('#skF_4', '#skF_5'))), inference(resolution, [status(thm)], [c_66, c_172])).
% 2.39/1.60  tff(c_191, plain, (k2_tarski('#skF_4', '#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_178])).
% 2.39/1.60  tff(c_222, plain, (k2_tarski('#skF_4', '#skF_5')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_187, c_191])).
% 2.39/1.60  tff(c_24, plain, (![D_17, B_13]: (r2_hidden(D_17, k2_tarski(D_17, B_13)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.39/1.60  tff(c_51, plain, (![B_33, A_34]: (~r2_hidden(B_33, A_34) | ~v1_xboole_0(A_34))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.39/1.60  tff(c_55, plain, (![D_17, B_13]: (~v1_xboole_0(k2_tarski(D_17, B_13)))), inference(resolution, [status(thm)], [c_24, c_51])).
% 2.39/1.60  tff(c_228, plain, (~v1_xboole_0('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_222, c_55])).
% 2.39/1.60  tff(c_239, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_203, c_228])).
% 2.39/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.39/1.60  
% 2.39/1.60  Inference rules
% 2.39/1.60  ----------------------
% 2.39/1.60  #Ref     : 0
% 2.39/1.60  #Sup     : 48
% 2.39/1.60  #Fact    : 0
% 2.39/1.60  #Define  : 0
% 2.39/1.60  #Split   : 0
% 2.39/1.60  #Chain   : 0
% 2.39/1.60  #Close   : 0
% 2.39/1.60  
% 2.39/1.60  Ordering : KBO
% 2.39/1.60  
% 2.39/1.60  Simplification rules
% 2.39/1.60  ----------------------
% 2.39/1.60  #Subsume      : 1
% 2.39/1.60  #Demod        : 21
% 2.39/1.60  #Tautology    : 33
% 2.39/1.60  #SimpNegUnit  : 0
% 2.39/1.60  #BackRed      : 6
% 2.39/1.60  
% 2.39/1.60  #Partial instantiations: 0
% 2.39/1.60  #Strategies tried      : 1
% 2.39/1.60  
% 2.39/1.60  Timing (in seconds)
% 2.39/1.60  ----------------------
% 2.39/1.60  Preprocessing        : 0.45
% 2.39/1.60  Parsing              : 0.22
% 2.39/1.60  CNF conversion       : 0.03
% 2.39/1.60  Main loop            : 0.24
% 2.39/1.60  Inferencing          : 0.08
% 2.39/1.60  Reduction            : 0.08
% 2.39/1.60  Demodulation         : 0.07
% 2.39/1.60  BG Simplification    : 0.02
% 2.39/1.61  Subsumption          : 0.04
% 2.39/1.61  Abstraction          : 0.02
% 2.39/1.61  MUC search           : 0.00
% 2.39/1.61  Cooper               : 0.00
% 2.39/1.61  Total                : 0.73
% 2.39/1.61  Index Insertion      : 0.00
% 2.39/1.61  Index Deletion       : 0.00
% 2.39/1.61  Index Matching       : 0.00
% 2.39/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------

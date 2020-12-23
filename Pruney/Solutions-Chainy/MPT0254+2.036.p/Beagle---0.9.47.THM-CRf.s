%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:24 EST 2020

% Result     : Theorem 2.04s
% Output     : CNFRefutation 2.04s
% Verified   : 
% Statistics : Number of formulae       :   51 (  72 expanded)
%              Number of leaves         :   28 (  37 expanded)
%              Depth                    :    8
%              Number of atoms          :   43 (  73 expanded)
%              Number of equality atoms :   16 (  28 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

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

tff(f_67,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

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

tff(f_55,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

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

tff(c_48,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_101,plain,(
    ! [B_46,A_47] : k2_xboole_0(B_46,A_47) = k2_xboole_0(A_47,B_46) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_18,plain,(
    ! [A_10,B_11] : r1_tarski(A_10,k2_xboole_0(A_10,B_11)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_152,plain,(
    ! [A_48,B_49] : r1_tarski(A_48,k2_xboole_0(B_49,A_48)) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_18])).

tff(c_161,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_152])).

tff(c_228,plain,(
    ! [B_56,A_57] :
      ( B_56 = A_57
      | ~ r1_tarski(B_56,A_57)
      | ~ r1_tarski(A_57,B_56) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_232,plain,
    ( k1_xboole_0 = '#skF_5'
    | ~ r1_tarski(k1_xboole_0,'#skF_5') ),
    inference(resolution,[status(thm)],[c_161,c_228])).

tff(c_246,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_232])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_262,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_8])).

tff(c_56,plain,(
    ! [A_32,B_33] : r1_tarski(A_32,k2_xboole_0(A_32,B_33)) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_59,plain,(
    r1_tarski(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_56])).

tff(c_236,plain,
    ( k1_tarski('#skF_4') = k1_xboole_0
    | ~ r1_tarski(k1_xboole_0,k1_tarski('#skF_4')) ),
    inference(resolution,[status(thm)],[c_59,c_228])).

tff(c_250,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_236])).

tff(c_268,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_246,c_250])).

tff(c_72,plain,(
    ! [A_42] : k2_tarski(A_42,A_42) = k1_tarski(A_42) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_61,plain,(
    ! [D_36,A_37] : r2_hidden(D_36,k2_tarski(A_37,D_36)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_65,plain,(
    ! [A_37,D_36] : ~ v1_xboole_0(k2_tarski(A_37,D_36)) ),
    inference(resolution,[status(thm)],[c_61,c_4])).

tff(c_80,plain,(
    ! [A_42] : ~ v1_xboole_0(k1_tarski(A_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_72,c_65])).

tff(c_280,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_268,c_80])).

tff(c_285,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_262,c_280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:35:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.04/1.28  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.28  
% 2.04/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.29  %$ r2_hidden > r1_tarski > v1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.04/1.29  
% 2.04/1.29  %Foreground sorts:
% 2.04/1.29  
% 2.04/1.29  
% 2.04/1.29  %Background operators:
% 2.04/1.29  
% 2.04/1.29  
% 2.04/1.29  %Foreground operators:
% 2.04/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.04/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.04/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.04/1.29  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.04/1.29  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.04/1.29  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.04/1.29  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.04/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.04/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.04/1.29  tff('#skF_5', type, '#skF_5': $i).
% 2.04/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.04/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.04/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.04/1.29  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.04/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.04/1.29  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.04/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.04/1.29  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.04/1.29  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.04/1.29  
% 2.04/1.30  tff(f_42, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.04/1.30  tff(f_67, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.04/1.30  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.04/1.30  tff(f_44, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.04/1.30  tff(f_40, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.04/1.30  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.04/1.30  tff(f_55, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.04/1.30  tff(f_53, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.04/1.30  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.04/1.30  tff(c_16, plain, (![A_9]: (r1_tarski(k1_xboole_0, A_9))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.04/1.30  tff(c_48, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_67])).
% 2.04/1.30  tff(c_101, plain, (![B_46, A_47]: (k2_xboole_0(B_46, A_47)=k2_xboole_0(A_47, B_46))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.04/1.30  tff(c_18, plain, (![A_10, B_11]: (r1_tarski(A_10, k2_xboole_0(A_10, B_11)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.04/1.30  tff(c_152, plain, (![A_48, B_49]: (r1_tarski(A_48, k2_xboole_0(B_49, A_48)))), inference(superposition, [status(thm), theory('equality')], [c_101, c_18])).
% 2.04/1.30  tff(c_161, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_152])).
% 2.04/1.30  tff(c_228, plain, (![B_56, A_57]: (B_56=A_57 | ~r1_tarski(B_56, A_57) | ~r1_tarski(A_57, B_56))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.04/1.30  tff(c_232, plain, (k1_xboole_0='#skF_5' | ~r1_tarski(k1_xboole_0, '#skF_5')), inference(resolution, [status(thm)], [c_161, c_228])).
% 2.04/1.30  tff(c_246, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_16, c_232])).
% 2.04/1.30  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.04/1.30  tff(c_262, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_246, c_8])).
% 2.04/1.30  tff(c_56, plain, (![A_32, B_33]: (r1_tarski(A_32, k2_xboole_0(A_32, B_33)))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.04/1.30  tff(c_59, plain, (r1_tarski(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_56])).
% 2.04/1.30  tff(c_236, plain, (k1_tarski('#skF_4')=k1_xboole_0 | ~r1_tarski(k1_xboole_0, k1_tarski('#skF_4'))), inference(resolution, [status(thm)], [c_59, c_228])).
% 2.04/1.30  tff(c_250, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_16, c_236])).
% 2.04/1.30  tff(c_268, plain, (k1_tarski('#skF_4')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_246, c_250])).
% 2.04/1.30  tff(c_72, plain, (![A_42]: (k2_tarski(A_42, A_42)=k1_tarski(A_42))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.04/1.30  tff(c_61, plain, (![D_36, A_37]: (r2_hidden(D_36, k2_tarski(A_37, D_36)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 2.04/1.30  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.04/1.30  tff(c_65, plain, (![A_37, D_36]: (~v1_xboole_0(k2_tarski(A_37, D_36)))), inference(resolution, [status(thm)], [c_61, c_4])).
% 2.04/1.30  tff(c_80, plain, (![A_42]: (~v1_xboole_0(k1_tarski(A_42)))), inference(superposition, [status(thm), theory('equality')], [c_72, c_65])).
% 2.04/1.30  tff(c_280, plain, (~v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_268, c_80])).
% 2.04/1.30  tff(c_285, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_262, c_280])).
% 2.04/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.04/1.30  
% 2.04/1.30  Inference rules
% 2.04/1.30  ----------------------
% 2.04/1.30  #Ref     : 0
% 2.04/1.30  #Sup     : 60
% 2.04/1.30  #Fact    : 0
% 2.04/1.30  #Define  : 0
% 2.04/1.30  #Split   : 0
% 2.04/1.30  #Chain   : 0
% 2.04/1.30  #Close   : 0
% 2.04/1.30  
% 2.04/1.30  Ordering : KBO
% 2.04/1.30  
% 2.04/1.30  Simplification rules
% 2.04/1.30  ----------------------
% 2.04/1.30  #Subsume      : 4
% 2.04/1.30  #Demod        : 24
% 2.04/1.30  #Tautology    : 38
% 2.04/1.30  #SimpNegUnit  : 0
% 2.04/1.30  #BackRed      : 6
% 2.04/1.30  
% 2.04/1.30  #Partial instantiations: 0
% 2.04/1.30  #Strategies tried      : 1
% 2.04/1.30  
% 2.04/1.30  Timing (in seconds)
% 2.04/1.30  ----------------------
% 2.04/1.30  Preprocessing        : 0.31
% 2.04/1.30  Parsing              : 0.16
% 2.04/1.30  CNF conversion       : 0.02
% 2.04/1.30  Main loop            : 0.23
% 2.04/1.30  Inferencing          : 0.07
% 2.04/1.30  Reduction            : 0.09
% 2.04/1.30  Demodulation         : 0.07
% 2.04/1.30  BG Simplification    : 0.01
% 2.04/1.30  Subsumption          : 0.04
% 2.04/1.30  Abstraction          : 0.01
% 2.04/1.30  MUC search           : 0.00
% 2.04/1.30  Cooper               : 0.00
% 2.04/1.30  Total                : 0.57
% 2.04/1.30  Index Insertion      : 0.00
% 2.04/1.30  Index Deletion       : 0.00
% 2.04/1.30  Index Matching       : 0.00
% 2.04/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------

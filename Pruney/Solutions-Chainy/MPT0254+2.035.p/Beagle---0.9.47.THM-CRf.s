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
% DateTime   : Thu Dec  3 09:51:24 EST 2020

% Result     : Theorem 2.22s
% Output     : CNFRefutation 2.38s
% Verified   : 
% Statistics : Number of formulae       :   52 ( 104 expanded)
%              Number of leaves         :   27 (  47 expanded)
%              Depth                    :    9
%              Number of atoms          :   41 ( 105 expanded)
%              Number of equality atoms :   20 (  58 expanded)
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

tff(f_46,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_44,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_69,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_34,axiom,(
    v1_xboole_0(k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',fc1_xboole_0)).

tff(f_59,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
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

tff(c_18,plain,(
    ! [A_11] : r1_tarski(k1_xboole_0,A_11) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_192,plain,(
    ! [A_50,B_51] :
      ( k2_xboole_0(A_50,B_51) = B_51
      | ~ r1_tarski(A_50,B_51) ) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_234,plain,(
    ! [A_53] : k2_xboole_0(k1_xboole_0,A_53) = A_53 ),
    inference(resolution,[status(thm)],[c_18,c_192])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_247,plain,(
    ! [A_53] : k2_xboole_0(A_53,k1_xboole_0) = A_53 ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_2])).

tff(c_48,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_101,plain,(
    ! [B_44,A_45] : k2_xboole_0(B_44,A_45) = k2_xboole_0(A_45,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_20,plain,(
    ! [A_12,B_13] : r1_tarski(A_12,k2_xboole_0(A_12,B_13)) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_152,plain,(
    ! [A_46,B_47] : r1_tarski(A_46,k2_xboole_0(B_47,A_46)) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_20])).

tff(c_161,plain,(
    r1_tarski('#skF_5',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_152])).

tff(c_211,plain,(
    k2_xboole_0('#skF_5',k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_161,c_192])).

tff(c_330,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_247,c_211])).

tff(c_8,plain,(
    v1_xboole_0(k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_34])).

tff(c_338,plain,(
    v1_xboole_0('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_8])).

tff(c_336,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_48])).

tff(c_250,plain,(
    ! [A_53] : k2_xboole_0(A_53,k1_xboole_0) = A_53 ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_2])).

tff(c_349,plain,(
    ! [A_53] : k2_xboole_0(A_53,'#skF_5') = A_53 ),
    inference(demodulation,[status(thm),theory(equality)],[c_330,c_250])).

tff(c_465,plain,(
    k1_tarski('#skF_4') = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_336,c_349])).

tff(c_40,plain,(
    ! [A_20] : k2_tarski(A_20,A_20) = k1_tarski(A_20) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_70,plain,(
    ! [D_35,A_36] : r2_hidden(D_35,k2_tarski(A_36,D_35)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_4,plain,(
    ! [B_6,A_3] :
      ( ~ r2_hidden(B_6,A_3)
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_86,plain,(
    ! [A_39,D_40] : ~ v1_xboole_0(k2_tarski(A_39,D_40)) ),
    inference(resolution,[status(thm)],[c_70,c_4])).

tff(c_88,plain,(
    ! [A_20] : ~ v1_xboole_0(k1_tarski(A_20)) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_86])).

tff(c_501,plain,(
    ~ v1_xboole_0('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_465,c_88])).

tff(c_506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_338,c_501])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:57:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.22/1.35  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.35  
% 2.22/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.22/1.36  %$ r2_hidden > r1_tarski > v1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 2.22/1.36  
% 2.22/1.36  %Foreground sorts:
% 2.22/1.36  
% 2.22/1.36  
% 2.22/1.36  %Background operators:
% 2.22/1.36  
% 2.22/1.36  
% 2.22/1.36  %Foreground operators:
% 2.22/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.22/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.22/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.22/1.36  tff('#skF_1', type, '#skF_1': $i > $i).
% 2.22/1.36  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.22/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.22/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.22/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.22/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.22/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.22/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.22/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.22/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.22/1.36  tff('#skF_4', type, '#skF_4': $i).
% 2.22/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.22/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.22/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.22/1.36  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 2.22/1.36  
% 2.38/1.37  tff(f_46, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 2.38/1.37  tff(f_44, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.38/1.37  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.38/1.37  tff(f_69, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 2.38/1.37  tff(f_48, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.38/1.37  tff(f_34, axiom, v1_xboole_0(k1_xboole_0), file('/export/starexec/sandbox/benchmark/theBenchmark.p', fc1_xboole_0)).
% 2.38/1.37  tff(f_59, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.38/1.37  tff(f_57, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 2.38/1.37  tff(f_33, axiom, (![A]: (v1_xboole_0(A) <=> (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_xboole_0)).
% 2.38/1.37  tff(c_18, plain, (![A_11]: (r1_tarski(k1_xboole_0, A_11))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.38/1.37  tff(c_192, plain, (![A_50, B_51]: (k2_xboole_0(A_50, B_51)=B_51 | ~r1_tarski(A_50, B_51))), inference(cnfTransformation, [status(thm)], [f_44])).
% 2.38/1.37  tff(c_234, plain, (![A_53]: (k2_xboole_0(k1_xboole_0, A_53)=A_53)), inference(resolution, [status(thm)], [c_18, c_192])).
% 2.38/1.37  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.38/1.37  tff(c_247, plain, (![A_53]: (k2_xboole_0(A_53, k1_xboole_0)=A_53)), inference(superposition, [status(thm), theory('equality')], [c_234, c_2])).
% 2.38/1.37  tff(c_48, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.38/1.37  tff(c_101, plain, (![B_44, A_45]: (k2_xboole_0(B_44, A_45)=k2_xboole_0(A_45, B_44))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.38/1.37  tff(c_20, plain, (![A_12, B_13]: (r1_tarski(A_12, k2_xboole_0(A_12, B_13)))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.38/1.37  tff(c_152, plain, (![A_46, B_47]: (r1_tarski(A_46, k2_xboole_0(B_47, A_46)))), inference(superposition, [status(thm), theory('equality')], [c_101, c_20])).
% 2.38/1.37  tff(c_161, plain, (r1_tarski('#skF_5', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_48, c_152])).
% 2.38/1.37  tff(c_211, plain, (k2_xboole_0('#skF_5', k1_xboole_0)=k1_xboole_0), inference(resolution, [status(thm)], [c_161, c_192])).
% 2.38/1.37  tff(c_330, plain, (k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_247, c_211])).
% 2.38/1.37  tff(c_8, plain, (v1_xboole_0(k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_34])).
% 2.38/1.37  tff(c_338, plain, (v1_xboole_0('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_330, c_8])).
% 2.38/1.37  tff(c_336, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_330, c_48])).
% 2.38/1.37  tff(c_250, plain, (![A_53]: (k2_xboole_0(A_53, k1_xboole_0)=A_53)), inference(superposition, [status(thm), theory('equality')], [c_234, c_2])).
% 2.38/1.37  tff(c_349, plain, (![A_53]: (k2_xboole_0(A_53, '#skF_5')=A_53)), inference(demodulation, [status(thm), theory('equality')], [c_330, c_250])).
% 2.38/1.37  tff(c_465, plain, (k1_tarski('#skF_4')='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_336, c_349])).
% 2.38/1.37  tff(c_40, plain, (![A_20]: (k2_tarski(A_20, A_20)=k1_tarski(A_20))), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.38/1.37  tff(c_70, plain, (![D_35, A_36]: (r2_hidden(D_35, k2_tarski(A_36, D_35)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.38/1.37  tff(c_4, plain, (![B_6, A_3]: (~r2_hidden(B_6, A_3) | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.38/1.37  tff(c_86, plain, (![A_39, D_40]: (~v1_xboole_0(k2_tarski(A_39, D_40)))), inference(resolution, [status(thm)], [c_70, c_4])).
% 2.38/1.37  tff(c_88, plain, (![A_20]: (~v1_xboole_0(k1_tarski(A_20)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_86])).
% 2.38/1.37  tff(c_501, plain, (~v1_xboole_0('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_465, c_88])).
% 2.38/1.37  tff(c_506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_338, c_501])).
% 2.38/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.38/1.37  
% 2.38/1.37  Inference rules
% 2.38/1.37  ----------------------
% 2.38/1.37  #Ref     : 0
% 2.38/1.37  #Sup     : 110
% 2.38/1.37  #Fact    : 0
% 2.38/1.37  #Define  : 0
% 2.38/1.37  #Split   : 0
% 2.38/1.37  #Chain   : 0
% 2.38/1.37  #Close   : 0
% 2.38/1.37  
% 2.38/1.37  Ordering : KBO
% 2.38/1.37  
% 2.38/1.37  Simplification rules
% 2.38/1.37  ----------------------
% 2.38/1.37  #Subsume      : 2
% 2.38/1.37  #Demod        : 51
% 2.38/1.37  #Tautology    : 82
% 2.38/1.37  #SimpNegUnit  : 0
% 2.38/1.37  #BackRed      : 10
% 2.38/1.37  
% 2.38/1.37  #Partial instantiations: 0
% 2.38/1.37  #Strategies tried      : 1
% 2.38/1.37  
% 2.38/1.37  Timing (in seconds)
% 2.38/1.37  ----------------------
% 2.38/1.37  Preprocessing        : 0.32
% 2.38/1.37  Parsing              : 0.17
% 2.38/1.37  CNF conversion       : 0.02
% 2.38/1.37  Main loop            : 0.22
% 2.38/1.37  Inferencing          : 0.07
% 2.38/1.37  Reduction            : 0.08
% 2.38/1.37  Demodulation         : 0.06
% 2.38/1.37  BG Simplification    : 0.01
% 2.38/1.37  Subsumption          : 0.04
% 2.38/1.37  Abstraction          : 0.01
% 2.38/1.37  MUC search           : 0.00
% 2.38/1.37  Cooper               : 0.00
% 2.38/1.37  Total                : 0.56
% 2.38/1.37  Index Insertion      : 0.00
% 2.38/1.37  Index Deletion       : 0.00
% 2.38/1.37  Index Matching       : 0.00
% 2.38/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------

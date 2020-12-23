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
% DateTime   : Thu Dec  3 09:54:33 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   43 (  52 expanded)
%              Number of leaves         :   24 (  29 expanded)
%              Depth                    :    8
%              Number of atoms          :   35 (  47 expanded)
%              Number of equality atoms :   20 (  29 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_41,axiom,(
    ! [A,B,C] : k4_xboole_0(k4_xboole_0(A,B),C) = k4_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t41_xboole_1)).

tff(c_34,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_28,plain,(
    ! [A_24,B_25] :
      ( r1_tarski(k1_tarski(A_24),B_25)
      | ~ r2_hidden(A_24,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_117,plain,(
    ! [A_39,B_40] :
      ( k2_xboole_0(A_39,B_40) = B_40
      | ~ r1_tarski(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_184,plain,(
    ! [A_52,B_53] :
      ( k2_xboole_0(k1_tarski(A_52),B_53) = B_53
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(resolution,[status(thm)],[c_28,c_117])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_197,plain,(
    ! [B_53,A_52] :
      ( k2_xboole_0(B_53,k1_tarski(A_52)) = B_53
      | ~ r2_hidden(A_52,B_53) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_184,c_2])).

tff(c_16,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_125,plain,(
    ! [B_4] : k2_xboole_0(B_4,B_4) = B_4 ),
    inference(resolution,[status(thm)],[c_8,c_117])).

tff(c_279,plain,(
    ! [A_59,B_60,C_61] : k4_xboole_0(k4_xboole_0(A_59,B_60),C_61) = k4_xboole_0(A_59,k2_xboole_0(B_60,C_61)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_322,plain,(
    ! [C_68,A_69,B_70] : k5_xboole_0(C_68,k4_xboole_0(A_69,k2_xboole_0(B_70,C_68))) = k2_xboole_0(C_68,k4_xboole_0(A_69,B_70)) ),
    inference(superposition,[status(thm),theory(equality)],[c_279,c_16])).

tff(c_341,plain,(
    ! [B_4,A_69] : k5_xboole_0(B_4,k4_xboole_0(A_69,B_4)) = k2_xboole_0(B_4,k4_xboole_0(A_69,B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_322])).

tff(c_352,plain,(
    ! [B_4,A_69] : k2_xboole_0(B_4,k4_xboole_0(A_69,B_4)) = k2_xboole_0(B_4,A_69) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_341])).

tff(c_32,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_36,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_32])).

tff(c_396,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_352,c_36])).

tff(c_397,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_396])).

tff(c_427,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_397])).

tff(c_431,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_427])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.08/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.08/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n016.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 17:10:49 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.27  
% 2.28/1.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.28  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.28/1.28  
% 2.28/1.28  %Foreground sorts:
% 2.28/1.28  
% 2.28/1.28  
% 2.28/1.28  %Background operators:
% 2.28/1.28  
% 2.28/1.28  
% 2.28/1.28  %Foreground operators:
% 2.28/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.28/1.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.28/1.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.28/1.28  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.28/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.28/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.28/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.28/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.28/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.28/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.28  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.28/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.28/1.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.28/1.28  
% 2.28/1.29  tff(f_62, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 2.28/1.29  tff(f_55, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.28/1.29  tff(f_39, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 2.28/1.29  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.28/1.29  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.28/1.29  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d10_xboole_0)).
% 2.28/1.29  tff(f_41, axiom, (![A, B, C]: (k4_xboole_0(k4_xboole_0(A, B), C) = k4_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t41_xboole_1)).
% 2.28/1.29  tff(c_34, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.28/1.29  tff(c_28, plain, (![A_24, B_25]: (r1_tarski(k1_tarski(A_24), B_25) | ~r2_hidden(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.28/1.29  tff(c_117, plain, (![A_39, B_40]: (k2_xboole_0(A_39, B_40)=B_40 | ~r1_tarski(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.28/1.29  tff(c_184, plain, (![A_52, B_53]: (k2_xboole_0(k1_tarski(A_52), B_53)=B_53 | ~r2_hidden(A_52, B_53))), inference(resolution, [status(thm)], [c_28, c_117])).
% 2.28/1.29  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.28/1.29  tff(c_197, plain, (![B_53, A_52]: (k2_xboole_0(B_53, k1_tarski(A_52))=B_53 | ~r2_hidden(A_52, B_53))), inference(superposition, [status(thm), theory('equality')], [c_184, c_2])).
% 2.28/1.29  tff(c_16, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.28/1.29  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.28/1.29  tff(c_125, plain, (![B_4]: (k2_xboole_0(B_4, B_4)=B_4)), inference(resolution, [status(thm)], [c_8, c_117])).
% 2.28/1.29  tff(c_279, plain, (![A_59, B_60, C_61]: (k4_xboole_0(k4_xboole_0(A_59, B_60), C_61)=k4_xboole_0(A_59, k2_xboole_0(B_60, C_61)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.28/1.29  tff(c_322, plain, (![C_68, A_69, B_70]: (k5_xboole_0(C_68, k4_xboole_0(A_69, k2_xboole_0(B_70, C_68)))=k2_xboole_0(C_68, k4_xboole_0(A_69, B_70)))), inference(superposition, [status(thm), theory('equality')], [c_279, c_16])).
% 2.28/1.29  tff(c_341, plain, (![B_4, A_69]: (k5_xboole_0(B_4, k4_xboole_0(A_69, B_4))=k2_xboole_0(B_4, k4_xboole_0(A_69, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_125, c_322])).
% 2.28/1.29  tff(c_352, plain, (![B_4, A_69]: (k2_xboole_0(B_4, k4_xboole_0(A_69, B_4))=k2_xboole_0(B_4, A_69))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_341])).
% 2.28/1.29  tff(c_32, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.28/1.29  tff(c_36, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_32])).
% 2.28/1.29  tff(c_396, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_352, c_36])).
% 2.28/1.29  tff(c_397, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_2, c_396])).
% 2.28/1.29  tff(c_427, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_197, c_397])).
% 2.28/1.29  tff(c_431, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_34, c_427])).
% 2.28/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.29  
% 2.28/1.29  Inference rules
% 2.28/1.29  ----------------------
% 2.28/1.29  #Ref     : 0
% 2.28/1.29  #Sup     : 89
% 2.28/1.29  #Fact    : 0
% 2.28/1.29  #Define  : 0
% 2.28/1.29  #Split   : 1
% 2.28/1.29  #Chain   : 0
% 2.28/1.29  #Close   : 0
% 2.28/1.29  
% 2.28/1.29  Ordering : KBO
% 2.28/1.29  
% 2.28/1.29  Simplification rules
% 2.28/1.29  ----------------------
% 2.28/1.29  #Subsume      : 9
% 2.28/1.29  #Demod        : 25
% 2.28/1.29  #Tautology    : 52
% 2.28/1.29  #SimpNegUnit  : 0
% 2.28/1.29  #BackRed      : 2
% 2.28/1.29  
% 2.28/1.29  #Partial instantiations: 0
% 2.28/1.29  #Strategies tried      : 1
% 2.28/1.29  
% 2.28/1.29  Timing (in seconds)
% 2.28/1.29  ----------------------
% 2.28/1.29  Preprocessing        : 0.30
% 2.28/1.29  Parsing              : 0.16
% 2.28/1.29  CNF conversion       : 0.02
% 2.28/1.29  Main loop            : 0.23
% 2.28/1.29  Inferencing          : 0.08
% 2.28/1.29  Reduction            : 0.08
% 2.28/1.29  Demodulation         : 0.06
% 2.28/1.29  BG Simplification    : 0.01
% 2.28/1.29  Subsumption          : 0.04
% 2.28/1.29  Abstraction          : 0.01
% 2.28/1.29  MUC search           : 0.00
% 2.28/1.29  Cooper               : 0.00
% 2.28/1.29  Total                : 0.55
% 2.28/1.29  Index Insertion      : 0.00
% 2.28/1.29  Index Deletion       : 0.00
% 2.28/1.29  Index Matching       : 0.00
% 2.28/1.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------

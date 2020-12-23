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
% DateTime   : Thu Dec  3 09:50:33 EST 2020

% Result     : Theorem 2.17s
% Output     : CNFRefutation 2.17s
% Verified   : 
% Statistics : Number of formulae       :   46 (  68 expanded)
%              Number of leaves         :   26 (  36 expanded)
%              Depth                    :    6
%              Number of atoms          :   34 (  59 expanded)
%              Number of equality atoms :   16 (  35 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_51,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_32,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_111,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_202,plain,(
    ! [A_60,B_61] : k3_tarski(k2_tarski(A_60,B_61)) = k2_xboole_0(B_61,A_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_111])).

tff(c_24,plain,(
    ! [A_37,B_38] : k3_tarski(k2_tarski(A_37,B_38)) = k2_xboole_0(A_37,B_38) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_208,plain,(
    ! [B_61,A_60] : k2_xboole_0(B_61,A_60) = k2_xboole_0(A_60,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_202,c_24])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_tarski(A_5,k2_xboole_0(A_5,B_6)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_154,plain,(
    ! [A_53,B_54] :
      ( k3_xboole_0(A_53,B_54) = A_53
      | ~ r1_tarski(A_53,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_166,plain,(
    ! [A_5,B_6] : k3_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = A_5 ),
    inference(resolution,[status(thm)],[c_6,c_154])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_165,plain,(
    k3_xboole_0(k2_xboole_0(k1_tarski('#skF_1'),'#skF_2'),'#skF_2') = k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') ),
    inference(resolution,[status(thm)],[c_34,c_154])).

tff(c_430,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_208,c_166,c_2,c_208,c_165])).

tff(c_10,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_228,plain,(
    ! [B_62,C_63,A_64] :
      ( r2_hidden(B_62,C_63)
      | ~ r1_tarski(k2_tarski(A_64,B_62),C_63) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_354,plain,(
    ! [B_71,A_72,B_73] : r2_hidden(B_71,k2_xboole_0(k2_tarski(A_72,B_71),B_73)) ),
    inference(resolution,[status(thm)],[c_6,c_228])).

tff(c_401,plain,(
    ! [A_77,B_78] : r2_hidden(A_77,k2_xboole_0(k1_tarski(A_77),B_78)) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_354])).

tff(c_405,plain,(
    ! [A_77,B_61] : r2_hidden(A_77,k2_xboole_0(B_61,k1_tarski(A_77))) ),
    inference(superposition,[status(thm),theory(equality)],[c_208,c_401])).

tff(c_435,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_430,c_405])).

tff(c_451,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_32,c_435])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n016.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:25:19 EST 2020
% 0.20/0.34  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.17/1.25  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.25  
% 2.17/1.25  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.26  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.17/1.26  
% 2.17/1.26  %Foreground sorts:
% 2.17/1.26  
% 2.17/1.26  
% 2.17/1.26  %Background operators:
% 2.17/1.26  
% 2.17/1.26  
% 2.17/1.26  %Foreground operators:
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.17/1.26  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.17/1.26  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.17/1.26  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.17/1.26  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.17/1.26  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.17/1.26  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.17/1.26  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.17/1.26  tff('#skF_2', type, '#skF_2': $i).
% 2.17/1.26  tff('#skF_1', type, '#skF_1': $i).
% 2.17/1.26  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.26  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.17/1.26  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.17/1.26  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.17/1.26  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.17/1.26  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.17/1.26  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.17/1.26  
% 2.17/1.27  tff(f_62, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 2.17/1.27  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.17/1.27  tff(f_51, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.17/1.27  tff(f_33, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 2.17/1.27  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.17/1.27  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.17/1.27  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.17/1.27  tff(f_57, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.17/1.27  tff(c_32, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.17/1.27  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.17/1.27  tff(c_111, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.17/1.27  tff(c_202, plain, (![A_60, B_61]: (k3_tarski(k2_tarski(A_60, B_61))=k2_xboole_0(B_61, A_60))), inference(superposition, [status(thm), theory('equality')], [c_8, c_111])).
% 2.17/1.27  tff(c_24, plain, (![A_37, B_38]: (k3_tarski(k2_tarski(A_37, B_38))=k2_xboole_0(A_37, B_38))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.17/1.27  tff(c_208, plain, (![B_61, A_60]: (k2_xboole_0(B_61, A_60)=k2_xboole_0(A_60, B_61))), inference(superposition, [status(thm), theory('equality')], [c_202, c_24])).
% 2.17/1.27  tff(c_6, plain, (![A_5, B_6]: (r1_tarski(A_5, k2_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.17/1.27  tff(c_154, plain, (![A_53, B_54]: (k3_xboole_0(A_53, B_54)=A_53 | ~r1_tarski(A_53, B_54))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.17/1.27  tff(c_166, plain, (![A_5, B_6]: (k3_xboole_0(A_5, k2_xboole_0(A_5, B_6))=A_5)), inference(resolution, [status(thm)], [c_6, c_154])).
% 2.17/1.27  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.17/1.27  tff(c_34, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.17/1.27  tff(c_165, plain, (k3_xboole_0(k2_xboole_0(k1_tarski('#skF_1'), '#skF_2'), '#skF_2')=k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')), inference(resolution, [status(thm)], [c_34, c_154])).
% 2.17/1.27  tff(c_430, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_208, c_166, c_2, c_208, c_165])).
% 2.17/1.27  tff(c_10, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.17/1.27  tff(c_228, plain, (![B_62, C_63, A_64]: (r2_hidden(B_62, C_63) | ~r1_tarski(k2_tarski(A_64, B_62), C_63))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.17/1.27  tff(c_354, plain, (![B_71, A_72, B_73]: (r2_hidden(B_71, k2_xboole_0(k2_tarski(A_72, B_71), B_73)))), inference(resolution, [status(thm)], [c_6, c_228])).
% 2.17/1.27  tff(c_401, plain, (![A_77, B_78]: (r2_hidden(A_77, k2_xboole_0(k1_tarski(A_77), B_78)))), inference(superposition, [status(thm), theory('equality')], [c_10, c_354])).
% 2.17/1.27  tff(c_405, plain, (![A_77, B_61]: (r2_hidden(A_77, k2_xboole_0(B_61, k1_tarski(A_77))))), inference(superposition, [status(thm), theory('equality')], [c_208, c_401])).
% 2.17/1.27  tff(c_435, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_430, c_405])).
% 2.17/1.27  tff(c_451, plain, $false, inference(negUnitSimplification, [status(thm)], [c_32, c_435])).
% 2.17/1.27  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.17/1.27  
% 2.17/1.27  Inference rules
% 2.17/1.27  ----------------------
% 2.17/1.27  #Ref     : 0
% 2.17/1.27  #Sup     : 102
% 2.17/1.27  #Fact    : 0
% 2.17/1.27  #Define  : 0
% 2.17/1.27  #Split   : 0
% 2.17/1.27  #Chain   : 0
% 2.17/1.27  #Close   : 0
% 2.17/1.27  
% 2.17/1.27  Ordering : KBO
% 2.17/1.27  
% 2.17/1.27  Simplification rules
% 2.17/1.27  ----------------------
% 2.17/1.27  #Subsume      : 4
% 2.17/1.27  #Demod        : 23
% 2.17/1.27  #Tautology    : 62
% 2.17/1.27  #SimpNegUnit  : 1
% 2.17/1.27  #BackRed      : 2
% 2.17/1.27  
% 2.17/1.27  #Partial instantiations: 0
% 2.17/1.27  #Strategies tried      : 1
% 2.17/1.27  
% 2.17/1.27  Timing (in seconds)
% 2.17/1.27  ----------------------
% 2.17/1.27  Preprocessing        : 0.31
% 2.17/1.27  Parsing              : 0.17
% 2.17/1.27  CNF conversion       : 0.02
% 2.17/1.27  Main loop            : 0.21
% 2.17/1.27  Inferencing          : 0.08
% 2.17/1.27  Reduction            : 0.08
% 2.17/1.27  Demodulation         : 0.06
% 2.17/1.27  BG Simplification    : 0.01
% 2.17/1.27  Subsumption          : 0.03
% 2.17/1.27  Abstraction          : 0.01
% 2.17/1.27  MUC search           : 0.00
% 2.17/1.27  Cooper               : 0.00
% 2.17/1.27  Total                : 0.55
% 2.17/1.27  Index Insertion      : 0.00
% 2.17/1.27  Index Deletion       : 0.00
% 2.17/1.27  Index Matching       : 0.00
% 2.17/1.27  BG Taut test         : 0.00
%------------------------------------------------------------------------------

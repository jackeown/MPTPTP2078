%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:16 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.26s
% Verified   : 
% Statistics : Number of formulae       :   40 (  51 expanded)
%              Number of leaves         :   23 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   37 (  52 expanded)
%              Number of equality atoms :   17 (  28 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

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

tff('#skF_3',type,(
    '#skF_3': $i )).

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

tff(f_56,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => B = k2_xboole_0(A,k4_xboole_0(B,A)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t45_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_28,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_26,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_196,plain,(
    ! [A_52,B_53,C_54] :
      ( r1_tarski(k2_tarski(A_52,B_53),C_54)
      | ~ r2_hidden(B_53,C_54)
      | ~ r2_hidden(A_52,C_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k4_xboole_0(B_4,A_3)) = k2_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,k4_xboole_0(B_6,A_5)) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_29,plain,(
    ! [A_5,B_6] :
      ( k2_xboole_0(A_5,B_6) = B_6
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4,c_6])).

tff(c_215,plain,(
    ! [A_55,B_56,C_57] :
      ( k2_xboole_0(k2_tarski(A_55,B_56),C_57) = C_57
      | ~ r2_hidden(B_56,C_57)
      | ~ r2_hidden(A_55,C_57) ) ),
    inference(resolution,[status(thm)],[c_196,c_29])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_73,plain,(
    ! [A_29,B_30] : k3_tarski(k2_tarski(A_29,B_30)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_88,plain,(
    ! [B_31,A_32] : k3_tarski(k2_tarski(B_31,A_32)) = k2_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_73])).

tff(c_16,plain,(
    ! [A_18,B_19] : k3_tarski(k2_tarski(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_94,plain,(
    ! [B_31,A_32] : k2_xboole_0(B_31,A_32) = k2_xboole_0(A_32,B_31) ),
    inference(superposition,[status(thm),theory(equality)],[c_88,c_16])).

tff(c_252,plain,(
    ! [C_58,A_59,B_60] :
      ( k2_xboole_0(C_58,k2_tarski(A_59,B_60)) = C_58
      | ~ r2_hidden(B_60,C_58)
      | ~ r2_hidden(A_59,C_58) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_215,c_94])).

tff(c_24,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_111,plain,(
    k2_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_24])).

tff(c_262,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_252,c_111])).

tff(c_294,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_26,c_262])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n007.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 20:16:06 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.36  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.36  
% 2.11/1.36  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.11/1.36  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_2 > #skF_3 > #skF_1
% 2.11/1.36  
% 2.11/1.36  %Foreground sorts:
% 2.11/1.36  
% 2.11/1.36  
% 2.11/1.36  %Background operators:
% 2.11/1.36  
% 2.11/1.36  
% 2.11/1.36  %Foreground operators:
% 2.11/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.11/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.11/1.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.11/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.36  tff('#skF_2', type, '#skF_2': $i).
% 2.11/1.36  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.36  tff('#skF_1', type, '#skF_1': $i).
% 2.11/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.11/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.11/1.36  
% 2.26/1.37  tff(f_56, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 2.26/1.37  tff(f_49, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.26/1.37  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.26/1.37  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (B = k2_xboole_0(A, k4_xboole_0(B, A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t45_xboole_1)).
% 2.26/1.37  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.26/1.37  tff(f_43, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.26/1.37  tff(c_28, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.26/1.37  tff(c_26, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.26/1.37  tff(c_196, plain, (![A_52, B_53, C_54]: (r1_tarski(k2_tarski(A_52, B_53), C_54) | ~r2_hidden(B_53, C_54) | ~r2_hidden(A_52, C_54))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.26/1.37  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k4_xboole_0(B_4, A_3))=k2_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.26/1.37  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k4_xboole_0(B_6, A_5))=B_6 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.26/1.37  tff(c_29, plain, (![A_5, B_6]: (k2_xboole_0(A_5, B_6)=B_6 | ~r1_tarski(A_5, B_6))), inference(demodulation, [status(thm), theory('equality')], [c_4, c_6])).
% 2.26/1.37  tff(c_215, plain, (![A_55, B_56, C_57]: (k2_xboole_0(k2_tarski(A_55, B_56), C_57)=C_57 | ~r2_hidden(B_56, C_57) | ~r2_hidden(A_55, C_57))), inference(resolution, [status(thm)], [c_196, c_29])).
% 2.26/1.37  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.26/1.37  tff(c_73, plain, (![A_29, B_30]: (k3_tarski(k2_tarski(A_29, B_30))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.26/1.37  tff(c_88, plain, (![B_31, A_32]: (k3_tarski(k2_tarski(B_31, A_32))=k2_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_8, c_73])).
% 2.26/1.37  tff(c_16, plain, (![A_18, B_19]: (k3_tarski(k2_tarski(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.26/1.37  tff(c_94, plain, (![B_31, A_32]: (k2_xboole_0(B_31, A_32)=k2_xboole_0(A_32, B_31))), inference(superposition, [status(thm), theory('equality')], [c_88, c_16])).
% 2.26/1.37  tff(c_252, plain, (![C_58, A_59, B_60]: (k2_xboole_0(C_58, k2_tarski(A_59, B_60))=C_58 | ~r2_hidden(B_60, C_58) | ~r2_hidden(A_59, C_58))), inference(superposition, [status(thm), theory('equality')], [c_215, c_94])).
% 2.26/1.37  tff(c_24, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_56])).
% 2.26/1.37  tff(c_111, plain, (k2_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_94, c_24])).
% 2.26/1.37  tff(c_262, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_252, c_111])).
% 2.26/1.37  tff(c_294, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_26, c_262])).
% 2.26/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.26/1.37  
% 2.26/1.37  Inference rules
% 2.26/1.37  ----------------------
% 2.26/1.37  #Ref     : 0
% 2.26/1.37  #Sup     : 66
% 2.26/1.37  #Fact    : 0
% 2.26/1.37  #Define  : 0
% 2.26/1.37  #Split   : 0
% 2.26/1.37  #Chain   : 0
% 2.26/1.37  #Close   : 0
% 2.26/1.37  
% 2.26/1.37  Ordering : KBO
% 2.26/1.37  
% 2.26/1.37  Simplification rules
% 2.26/1.37  ----------------------
% 2.26/1.37  #Subsume      : 9
% 2.26/1.37  #Demod        : 7
% 2.26/1.37  #Tautology    : 38
% 2.26/1.37  #SimpNegUnit  : 0
% 2.26/1.37  #BackRed      : 1
% 2.26/1.37  
% 2.26/1.37  #Partial instantiations: 0
% 2.26/1.37  #Strategies tried      : 1
% 2.26/1.37  
% 2.26/1.37  Timing (in seconds)
% 2.26/1.37  ----------------------
% 2.26/1.38  Preprocessing        : 0.34
% 2.26/1.38  Parsing              : 0.18
% 2.26/1.38  CNF conversion       : 0.02
% 2.26/1.38  Main loop            : 0.21
% 2.26/1.38  Inferencing          : 0.09
% 2.26/1.38  Reduction            : 0.07
% 2.26/1.38  Demodulation         : 0.06
% 2.26/1.38  BG Simplification    : 0.01
% 2.26/1.38  Subsumption          : 0.03
% 2.26/1.38  Abstraction          : 0.02
% 2.26/1.38  MUC search           : 0.00
% 2.26/1.38  Cooper               : 0.00
% 2.26/1.38  Total                : 0.58
% 2.26/1.38  Index Insertion      : 0.00
% 2.26/1.38  Index Deletion       : 0.00
% 2.26/1.38  Index Matching       : 0.00
% 2.26/1.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------

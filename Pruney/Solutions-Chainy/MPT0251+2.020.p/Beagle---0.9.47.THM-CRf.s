%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:48 EST 2020

% Result     : Theorem 1.72s
% Output     : CNFRefutation 1.72s
% Verified   : 
% Statistics : Number of formulae       :   41 (  43 expanded)
%              Number of leaves         :   22 (  24 expanded)
%              Depth                    :    6
%              Number of atoms          :   38 (  41 expanded)
%              Number of equality atoms :   21 (  23 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_37,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_49,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_43,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_26,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_10,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_281,plain,(
    ! [A_51,B_52,C_53] :
      ( r1_tarski(k2_tarski(A_51,B_52),C_53)
      | ~ r2_hidden(B_52,C_53)
      | ~ r2_hidden(A_51,C_53) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_303,plain,(
    ! [A_54,C_55] :
      ( r1_tarski(k1_tarski(A_54),C_55)
      | ~ r2_hidden(A_54,C_55)
      | ~ r2_hidden(A_54,C_55) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_281])).

tff(c_6,plain,(
    ! [A_5,B_6] :
      ( k3_xboole_0(A_5,B_6) = A_5
      | ~ r1_tarski(A_5,B_6) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_352,plain,(
    ! [A_59,C_60] :
      ( k3_xboole_0(k1_tarski(A_59),C_60) = k1_tarski(A_59)
      | ~ r2_hidden(A_59,C_60) ) ),
    inference(resolution,[status(thm)],[c_303,c_6])).

tff(c_78,plain,(
    ! [B_25,A_26] : k3_xboole_0(B_25,A_26) = k3_xboole_0(A_26,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4,plain,(
    ! [A_3,B_4] : k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_93,plain,(
    ! [A_26,B_25] : k2_xboole_0(A_26,k3_xboole_0(B_25,A_26)) = A_26 ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_4])).

tff(c_382,plain,(
    ! [C_61,A_62] :
      ( k2_xboole_0(C_61,k1_tarski(A_62)) = C_61
      | ~ r2_hidden(A_62,C_61) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_352,c_93])).

tff(c_8,plain,(
    ! [B_8,A_7] : k2_tarski(B_8,A_7) = k2_tarski(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_146,plain,(
    ! [A_31,B_32] : k3_tarski(k2_tarski(A_31,B_32)) = k2_xboole_0(A_31,B_32) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_190,plain,(
    ! [A_36,B_37] : k3_tarski(k2_tarski(A_36,B_37)) = k2_xboole_0(B_37,A_36) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_146])).

tff(c_16,plain,(
    ! [A_15,B_16] : k3_tarski(k2_tarski(A_15,B_16)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_196,plain,(
    ! [B_37,A_36] : k2_xboole_0(B_37,A_36) = k2_xboole_0(A_36,B_37) ),
    inference(superposition,[status(thm),theory(equality)],[c_190,c_16])).

tff(c_24,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_216,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_196,c_24])).

tff(c_388,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_216])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_388])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n021.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 19:37:34 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.72/1.15  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.15  
% 1.72/1.15  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.16  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 1.72/1.16  
% 1.72/1.16  %Foreground sorts:
% 1.72/1.16  
% 1.72/1.16  
% 1.72/1.16  %Background operators:
% 1.72/1.16  
% 1.72/1.16  
% 1.72/1.16  %Foreground operators:
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.72/1.16  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.72/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.72/1.16  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.72/1.16  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.72/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.72/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.72/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.72/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.72/1.16  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.72/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.72/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.72/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.72/1.16  
% 1.72/1.17  tff(f_54, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 1.72/1.17  tff(f_37, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.72/1.17  tff(f_49, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 1.72/1.17  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 1.72/1.17  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 1.72/1.17  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 1.72/1.17  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 1.72/1.17  tff(f_43, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 1.72/1.17  tff(c_26, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.72/1.17  tff(c_10, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.72/1.17  tff(c_281, plain, (![A_51, B_52, C_53]: (r1_tarski(k2_tarski(A_51, B_52), C_53) | ~r2_hidden(B_52, C_53) | ~r2_hidden(A_51, C_53))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.72/1.17  tff(c_303, plain, (![A_54, C_55]: (r1_tarski(k1_tarski(A_54), C_55) | ~r2_hidden(A_54, C_55) | ~r2_hidden(A_54, C_55))), inference(superposition, [status(thm), theory('equality')], [c_10, c_281])).
% 1.72/1.17  tff(c_6, plain, (![A_5, B_6]: (k3_xboole_0(A_5, B_6)=A_5 | ~r1_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.72/1.17  tff(c_352, plain, (![A_59, C_60]: (k3_xboole_0(k1_tarski(A_59), C_60)=k1_tarski(A_59) | ~r2_hidden(A_59, C_60))), inference(resolution, [status(thm)], [c_303, c_6])).
% 1.72/1.17  tff(c_78, plain, (![B_25, A_26]: (k3_xboole_0(B_25, A_26)=k3_xboole_0(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.72/1.17  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, k3_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.72/1.17  tff(c_93, plain, (![A_26, B_25]: (k2_xboole_0(A_26, k3_xboole_0(B_25, A_26))=A_26)), inference(superposition, [status(thm), theory('equality')], [c_78, c_4])).
% 1.72/1.17  tff(c_382, plain, (![C_61, A_62]: (k2_xboole_0(C_61, k1_tarski(A_62))=C_61 | ~r2_hidden(A_62, C_61))), inference(superposition, [status(thm), theory('equality')], [c_352, c_93])).
% 1.72/1.17  tff(c_8, plain, (![B_8, A_7]: (k2_tarski(B_8, A_7)=k2_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.72/1.17  tff(c_146, plain, (![A_31, B_32]: (k3_tarski(k2_tarski(A_31, B_32))=k2_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.72/1.17  tff(c_190, plain, (![A_36, B_37]: (k3_tarski(k2_tarski(A_36, B_37))=k2_xboole_0(B_37, A_36))), inference(superposition, [status(thm), theory('equality')], [c_8, c_146])).
% 1.72/1.17  tff(c_16, plain, (![A_15, B_16]: (k3_tarski(k2_tarski(A_15, B_16))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.72/1.17  tff(c_196, plain, (![B_37, A_36]: (k2_xboole_0(B_37, A_36)=k2_xboole_0(A_36, B_37))), inference(superposition, [status(thm), theory('equality')], [c_190, c_16])).
% 1.72/1.17  tff(c_24, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.72/1.17  tff(c_216, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_196, c_24])).
% 1.72/1.17  tff(c_388, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_382, c_216])).
% 1.72/1.17  tff(c_418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_388])).
% 1.72/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.72/1.17  
% 1.72/1.17  Inference rules
% 1.72/1.17  ----------------------
% 1.72/1.17  #Ref     : 0
% 1.72/1.17  #Sup     : 98
% 1.72/1.17  #Fact    : 0
% 1.72/1.17  #Define  : 0
% 1.72/1.17  #Split   : 0
% 1.72/1.17  #Chain   : 0
% 1.72/1.17  #Close   : 0
% 1.72/1.17  
% 1.72/1.17  Ordering : KBO
% 1.72/1.17  
% 1.72/1.17  Simplification rules
% 1.72/1.17  ----------------------
% 1.72/1.17  #Subsume      : 9
% 1.72/1.17  #Demod        : 11
% 1.72/1.17  #Tautology    : 58
% 1.72/1.17  #SimpNegUnit  : 0
% 1.72/1.17  #BackRed      : 1
% 1.72/1.17  
% 1.72/1.17  #Partial instantiations: 0
% 1.72/1.17  #Strategies tried      : 1
% 1.72/1.17  
% 1.72/1.17  Timing (in seconds)
% 1.72/1.17  ----------------------
% 1.72/1.17  Preprocessing        : 0.26
% 1.72/1.17  Parsing              : 0.13
% 1.72/1.17  CNF conversion       : 0.02
% 1.72/1.17  Main loop            : 0.19
% 1.72/1.17  Inferencing          : 0.08
% 1.72/1.17  Reduction            : 0.06
% 1.72/1.17  Demodulation         : 0.05
% 1.72/1.17  BG Simplification    : 0.01
% 1.72/1.17  Subsumption          : 0.03
% 1.72/1.17  Abstraction          : 0.01
% 1.72/1.17  MUC search           : 0.00
% 1.72/1.17  Cooper               : 0.00
% 1.72/1.17  Total                : 0.47
% 1.72/1.17  Index Insertion      : 0.00
% 1.72/1.17  Index Deletion       : 0.00
% 1.72/1.17  Index Matching       : 0.00
% 1.72/1.17  BG Taut test         : 0.00
%------------------------------------------------------------------------------

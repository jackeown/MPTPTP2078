%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:53 EST 2020

% Result     : Theorem 2.09s
% Output     : CNFRefutation 2.09s
% Verified   : 
% Statistics : Number of formulae       :   44 (  46 expanded)
%              Number of leaves         :   27 (  29 expanded)
%              Depth                    :    6
%              Number of atoms          :   32 (  35 expanded)
%              Number of equality atoms :   19 (  21 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

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
        ( r2_hidden(A,B)
       => k2_xboole_0(k1_tarski(A),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : k2_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t1_boole)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( k4_xboole_0(A,B) = k1_xboole_0
    <=> r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l32_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_57,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_36,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_30,plain,(
    ! [A_34,B_35] :
      ( r1_tarski(k1_tarski(A_34),B_35)
      | ~ r2_hidden(A_34,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_134,plain,(
    ! [A_51,B_52] :
      ( k4_xboole_0(A_51,B_52) = k1_xboole_0
      | ~ r1_tarski(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_406,plain,(
    ! [A_73,B_74] :
      ( k4_xboole_0(k1_tarski(A_73),B_74) = k1_xboole_0
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(resolution,[status(thm)],[c_30,c_134])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(A_6,k4_xboole_0(B_7,A_6)) = k2_xboole_0(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_416,plain,(
    ! [B_74,A_73] :
      ( k2_xboole_0(B_74,k1_tarski(A_73)) = k2_xboole_0(B_74,k1_xboole_0)
      | ~ r2_hidden(A_73,B_74) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_10])).

tff(c_451,plain,(
    ! [B_83,A_84] :
      ( k2_xboole_0(B_83,k1_tarski(A_84)) = B_83
      | ~ r2_hidden(A_84,B_83) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_416])).

tff(c_12,plain,(
    ! [B_9,A_8] : k2_tarski(B_9,A_8) = k2_tarski(A_8,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_89,plain,(
    ! [A_44,B_45] : k3_tarski(k2_tarski(A_44,B_45)) = k2_xboole_0(A_44,B_45) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_153,plain,(
    ! [A_55,B_56] : k3_tarski(k2_tarski(A_55,B_56)) = k2_xboole_0(B_56,A_55) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_89])).

tff(c_32,plain,(
    ! [A_36,B_37] : k3_tarski(k2_tarski(A_36,B_37)) = k2_xboole_0(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_159,plain,(
    ! [B_56,A_55] : k2_xboole_0(B_56,A_55) = k2_xboole_0(A_55,B_56) ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_32])).

tff(c_34,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_179,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_34])).

tff(c_457,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_451,c_179])).

tff(c_495,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_457])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n011.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:28:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.09/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.29  
% 2.09/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.30  %$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 2.09/1.30  
% 2.09/1.30  %Foreground sorts:
% 2.09/1.30  
% 2.09/1.30  
% 2.09/1.30  %Background operators:
% 2.09/1.30  
% 2.09/1.30  
% 2.09/1.30  %Foreground operators:
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.09/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.09/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.09/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.09/1.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.09/1.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.09/1.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.09/1.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.09/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.09/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.09/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.09/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.09/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.09/1.30  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.09/1.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.09/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.09/1.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.09/1.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.09/1.30  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.09/1.30  
% 2.09/1.30  tff(f_62, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k1_tarski(A), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_zfmisc_1)).
% 2.09/1.30  tff(f_33, axiom, (![A]: (k2_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t1_boole)).
% 2.09/1.30  tff(f_55, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 2.09/1.30  tff(f_29, axiom, (![A, B]: ((k4_xboole_0(A, B) = k1_xboole_0) <=> r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l32_xboole_1)).
% 2.09/1.30  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.09/1.30  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.09/1.30  tff(f_57, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.09/1.30  tff(c_36, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.09/1.30  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.09/1.30  tff(c_30, plain, (![A_34, B_35]: (r1_tarski(k1_tarski(A_34), B_35) | ~r2_hidden(A_34, B_35))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.09/1.30  tff(c_134, plain, (![A_51, B_52]: (k4_xboole_0(A_51, B_52)=k1_xboole_0 | ~r1_tarski(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.09/1.30  tff(c_406, plain, (![A_73, B_74]: (k4_xboole_0(k1_tarski(A_73), B_74)=k1_xboole_0 | ~r2_hidden(A_73, B_74))), inference(resolution, [status(thm)], [c_30, c_134])).
% 2.09/1.30  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(A_6, k4_xboole_0(B_7, A_6))=k2_xboole_0(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.09/1.30  tff(c_416, plain, (![B_74, A_73]: (k2_xboole_0(B_74, k1_tarski(A_73))=k2_xboole_0(B_74, k1_xboole_0) | ~r2_hidden(A_73, B_74))), inference(superposition, [status(thm), theory('equality')], [c_406, c_10])).
% 2.09/1.30  tff(c_451, plain, (![B_83, A_84]: (k2_xboole_0(B_83, k1_tarski(A_84))=B_83 | ~r2_hidden(A_84, B_83))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_416])).
% 2.09/1.30  tff(c_12, plain, (![B_9, A_8]: (k2_tarski(B_9, A_8)=k2_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.09/1.30  tff(c_89, plain, (![A_44, B_45]: (k3_tarski(k2_tarski(A_44, B_45))=k2_xboole_0(A_44, B_45))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.09/1.30  tff(c_153, plain, (![A_55, B_56]: (k3_tarski(k2_tarski(A_55, B_56))=k2_xboole_0(B_56, A_55))), inference(superposition, [status(thm), theory('equality')], [c_12, c_89])).
% 2.09/1.30  tff(c_32, plain, (![A_36, B_37]: (k3_tarski(k2_tarski(A_36, B_37))=k2_xboole_0(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.09/1.30  tff(c_159, plain, (![B_56, A_55]: (k2_xboole_0(B_56, A_55)=k2_xboole_0(A_55, B_56))), inference(superposition, [status(thm), theory('equality')], [c_153, c_32])).
% 2.09/1.30  tff(c_34, plain, (k2_xboole_0(k1_tarski('#skF_1'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.09/1.30  tff(c_179, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_159, c_34])).
% 2.09/1.30  tff(c_457, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_451, c_179])).
% 2.09/1.30  tff(c_495, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_457])).
% 2.09/1.30  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.09/1.30  
% 2.09/1.30  Inference rules
% 2.09/1.30  ----------------------
% 2.09/1.30  #Ref     : 0
% 2.09/1.30  #Sup     : 106
% 2.09/1.30  #Fact    : 0
% 2.09/1.30  #Define  : 0
% 2.09/1.30  #Split   : 0
% 2.09/1.30  #Chain   : 0
% 2.09/1.30  #Close   : 0
% 2.09/1.30  
% 2.09/1.30  Ordering : KBO
% 2.09/1.30  
% 2.09/1.30  Simplification rules
% 2.09/1.31  ----------------------
% 2.09/1.31  #Subsume      : 3
% 2.09/1.31  #Demod        : 29
% 2.09/1.31  #Tautology    : 82
% 2.09/1.31  #SimpNegUnit  : 0
% 2.09/1.31  #BackRed      : 1
% 2.09/1.31  
% 2.09/1.31  #Partial instantiations: 0
% 2.09/1.31  #Strategies tried      : 1
% 2.09/1.31  
% 2.09/1.31  Timing (in seconds)
% 2.09/1.31  ----------------------
% 2.09/1.31  Preprocessing        : 0.32
% 2.09/1.31  Parsing              : 0.18
% 2.09/1.31  CNF conversion       : 0.02
% 2.09/1.31  Main loop            : 0.20
% 2.09/1.31  Inferencing          : 0.08
% 2.09/1.31  Reduction            : 0.07
% 2.09/1.31  Demodulation         : 0.06
% 2.09/1.31  BG Simplification    : 0.01
% 2.09/1.31  Subsumption          : 0.03
% 2.09/1.31  Abstraction          : 0.01
% 2.09/1.31  MUC search           : 0.00
% 2.09/1.31  Cooper               : 0.00
% 2.09/1.31  Total                : 0.55
% 2.09/1.31  Index Insertion      : 0.00
% 2.09/1.31  Index Deletion       : 0.00
% 2.09/1.31  Index Matching       : 0.00
% 2.09/1.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------

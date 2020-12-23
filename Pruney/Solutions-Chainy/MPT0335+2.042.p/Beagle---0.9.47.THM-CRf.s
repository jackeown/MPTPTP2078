%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n005.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:59 EST 2020

% Result     : Theorem 3.91s
% Output     : CNFRefutation 3.91s
% Verified   : 
% Statistics : Number of formulae       :   43 (  47 expanded)
%              Number of leaves         :   24 (  28 expanded)
%              Depth                    :    7
%              Number of atoms          :   40 (  54 expanded)
%              Number of equality atoms :   20 (  27 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_53,axiom,(
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
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_28,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_30,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_8,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_398,plain,(
    ! [A_65,B_66,C_67] :
      ( r1_tarski(k2_tarski(A_65,B_66),C_67)
      | ~ r2_hidden(B_66,C_67)
      | ~ r2_hidden(A_65,C_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_1610,plain,(
    ! [A_89,C_90] :
      ( r1_tarski(k1_tarski(A_89),C_90)
      | ~ r2_hidden(A_89,C_90)
      | ~ r2_hidden(A_89,C_90) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_398])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1628,plain,(
    ! [A_97,C_98] :
      ( k3_xboole_0(k1_tarski(A_97),C_98) = k1_tarski(A_97)
      | ~ r2_hidden(A_97,C_98) ) ),
    inference(resolution,[status(thm)],[c_1610,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1743,plain,(
    ! [C_99,A_100] :
      ( k3_xboole_0(C_99,k1_tarski(A_100)) = k1_tarski(A_100)
      | ~ r2_hidden(A_100,C_99) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1628,c_2])).

tff(c_32,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_34,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_100,plain,(
    ! [A_42,B_43] :
      ( k3_xboole_0(A_42,B_43) = A_42
      | ~ r1_tarski(A_42,B_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_104,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_34,c_100])).

tff(c_136,plain,(
    ! [A_57,B_58,C_59] : k3_xboole_0(k3_xboole_0(A_57,B_58),C_59) = k3_xboole_0(A_57,k3_xboole_0(B_58,C_59)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_182,plain,(
    ! [C_60] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_60)) = k3_xboole_0('#skF_1',C_60) ),
    inference(superposition,[status(thm),theory(equality)],[c_104,c_136])).

tff(c_202,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_4')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_182])).

tff(c_1795,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1743,c_202])).

tff(c_1862,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_1795])).

tff(c_1864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_28,c_1862])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n005.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:36:47 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.91/1.67  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.67  
% 3.91/1.67  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.67  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 3.91/1.67  
% 3.91/1.67  %Foreground sorts:
% 3.91/1.67  
% 3.91/1.67  
% 3.91/1.67  %Background operators:
% 3.91/1.67  
% 3.91/1.67  
% 3.91/1.67  %Foreground operators:
% 3.91/1.67  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.91/1.67  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.91/1.67  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.91/1.67  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.91/1.67  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.91/1.67  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.91/1.67  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.91/1.67  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.91/1.67  tff('#skF_2', type, '#skF_2': $i).
% 3.91/1.67  tff('#skF_3', type, '#skF_3': $i).
% 3.91/1.67  tff('#skF_1', type, '#skF_1': $i).
% 3.91/1.67  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.91/1.67  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.91/1.67  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.91/1.67  tff('#skF_4', type, '#skF_4': $i).
% 3.91/1.67  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.91/1.67  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.91/1.67  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.91/1.67  
% 3.91/1.68  tff(f_62, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 3.91/1.68  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.91/1.68  tff(f_53, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.91/1.68  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.91/1.68  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.91/1.68  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 3.91/1.68  tff(c_28, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.91/1.68  tff(c_30, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.91/1.68  tff(c_8, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.91/1.68  tff(c_398, plain, (![A_65, B_66, C_67]: (r1_tarski(k2_tarski(A_65, B_66), C_67) | ~r2_hidden(B_66, C_67) | ~r2_hidden(A_65, C_67))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.91/1.68  tff(c_1610, plain, (![A_89, C_90]: (r1_tarski(k1_tarski(A_89), C_90) | ~r2_hidden(A_89, C_90) | ~r2_hidden(A_89, C_90))), inference(superposition, [status(thm), theory('equality')], [c_8, c_398])).
% 3.91/1.68  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.91/1.68  tff(c_1628, plain, (![A_97, C_98]: (k3_xboole_0(k1_tarski(A_97), C_98)=k1_tarski(A_97) | ~r2_hidden(A_97, C_98))), inference(resolution, [status(thm)], [c_1610, c_6])).
% 3.91/1.68  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.91/1.68  tff(c_1743, plain, (![C_99, A_100]: (k3_xboole_0(C_99, k1_tarski(A_100))=k1_tarski(A_100) | ~r2_hidden(A_100, C_99))), inference(superposition, [status(thm), theory('equality')], [c_1628, c_2])).
% 3.91/1.68  tff(c_32, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.91/1.68  tff(c_34, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.91/1.68  tff(c_100, plain, (![A_42, B_43]: (k3_xboole_0(A_42, B_43)=A_42 | ~r1_tarski(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.91/1.68  tff(c_104, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_34, c_100])).
% 3.91/1.68  tff(c_136, plain, (![A_57, B_58, C_59]: (k3_xboole_0(k3_xboole_0(A_57, B_58), C_59)=k3_xboole_0(A_57, k3_xboole_0(B_58, C_59)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.91/1.68  tff(c_182, plain, (![C_60]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_60))=k3_xboole_0('#skF_1', C_60))), inference(superposition, [status(thm), theory('equality')], [c_104, c_136])).
% 3.91/1.68  tff(c_202, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_4'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_32, c_182])).
% 3.91/1.68  tff(c_1795, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1743, c_202])).
% 3.91/1.68  tff(c_1862, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_30, c_1795])).
% 3.91/1.68  tff(c_1864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_28, c_1862])).
% 3.91/1.68  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.91/1.68  
% 3.91/1.68  Inference rules
% 3.91/1.68  ----------------------
% 3.91/1.68  #Ref     : 0
% 3.91/1.68  #Sup     : 452
% 3.91/1.68  #Fact    : 0
% 3.91/1.68  #Define  : 0
% 3.91/1.68  #Split   : 0
% 3.91/1.68  #Chain   : 0
% 3.91/1.68  #Close   : 0
% 3.91/1.68  
% 3.91/1.68  Ordering : KBO
% 3.91/1.68  
% 3.91/1.68  Simplification rules
% 3.91/1.68  ----------------------
% 3.91/1.68  #Subsume      : 47
% 3.91/1.68  #Demod        : 302
% 3.91/1.68  #Tautology    : 183
% 3.91/1.68  #SimpNegUnit  : 1
% 3.91/1.68  #BackRed      : 1
% 3.91/1.68  
% 3.91/1.68  #Partial instantiations: 0
% 3.91/1.68  #Strategies tried      : 1
% 3.91/1.68  
% 3.91/1.68  Timing (in seconds)
% 3.91/1.68  ----------------------
% 3.91/1.69  Preprocessing        : 0.31
% 3.91/1.69  Parsing              : 0.16
% 3.91/1.69  CNF conversion       : 0.02
% 3.91/1.69  Main loop            : 0.63
% 3.91/1.69  Inferencing          : 0.19
% 3.91/1.69  Reduction            : 0.31
% 3.91/1.69  Demodulation         : 0.27
% 3.91/1.69  BG Simplification    : 0.03
% 3.91/1.69  Subsumption          : 0.08
% 3.91/1.69  Abstraction          : 0.03
% 3.91/1.69  MUC search           : 0.00
% 3.91/1.69  Cooper               : 0.00
% 3.91/1.69  Total                : 0.96
% 3.91/1.69  Index Insertion      : 0.00
% 3.91/1.69  Index Deletion       : 0.00
% 3.91/1.69  Index Matching       : 0.00
% 3.91/1.69  BG Taut test         : 0.00
%------------------------------------------------------------------------------

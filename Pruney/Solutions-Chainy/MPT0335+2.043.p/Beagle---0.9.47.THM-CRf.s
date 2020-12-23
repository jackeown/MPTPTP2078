%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:59 EST 2020

% Result     : Theorem 6.98s
% Output     : CNFRefutation 6.98s
% Verified   : 
% Statistics : Number of formulae       :   38 (  45 expanded)
%              Number of leaves         :   20 (  25 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  60 expanded)
%              Number of equality atoms :   22 (  32 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_35,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r2_hidden(C,B) )
     => k3_xboole_0(k2_tarski(A,C),B) = k2_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(c_16,plain,(
    k3_xboole_0('#skF_1','#skF_3') != k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_18,plain,(
    r2_hidden('#skF_4','#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_8,plain,(
    ! [A_8] : k2_tarski(A_8,A_8) = k1_tarski(A_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_161,plain,(
    ! [A_30,C_31,B_32] :
      ( k3_xboole_0(k2_tarski(A_30,C_31),B_32) = k2_tarski(A_30,C_31)
      | ~ r2_hidden(C_31,B_32)
      | ~ r2_hidden(A_30,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_4607,plain,(
    ! [B_69,A_70,C_71] :
      ( k3_xboole_0(B_69,k2_tarski(A_70,C_71)) = k2_tarski(A_70,C_71)
      | ~ r2_hidden(C_71,B_69)
      | ~ r2_hidden(A_70,B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_161,c_2])).

tff(c_4735,plain,(
    ! [B_69,A_8] :
      ( k3_xboole_0(B_69,k1_tarski(A_8)) = k2_tarski(A_8,A_8)
      | ~ r2_hidden(A_8,B_69)
      | ~ r2_hidden(A_8,B_69) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_4607])).

tff(c_6687,plain,(
    ! [B_84,A_85] :
      ( k3_xboole_0(B_84,k1_tarski(A_85)) = k1_tarski(A_85)
      | ~ r2_hidden(A_85,B_84)
      | ~ r2_hidden(A_85,B_84) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4735])).

tff(c_20,plain,(
    k3_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_22,plain,(
    r1_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_97,plain,(
    ! [A_22,B_23] :
      ( k3_xboole_0(A_22,B_23) = A_22
      | ~ r1_tarski(A_22,B_23) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_101,plain,(
    k3_xboole_0('#skF_1','#skF_2') = '#skF_1' ),
    inference(resolution,[status(thm)],[c_22,c_97])).

tff(c_115,plain,(
    ! [A_27,B_28,C_29] : k3_xboole_0(k3_xboole_0(A_27,B_28),C_29) = k3_xboole_0(A_27,k3_xboole_0(B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_191,plain,(
    ! [C_33] : k3_xboole_0('#skF_1',k3_xboole_0('#skF_2',C_33)) = k3_xboole_0('#skF_1',C_33) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_115])).

tff(c_211,plain,(
    k3_xboole_0('#skF_1',k1_tarski('#skF_4')) = k3_xboole_0('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_191])).

tff(c_6795,plain,
    ( k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4')
    | ~ r2_hidden('#skF_4','#skF_1')
    | ~ r2_hidden('#skF_4','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_6687,c_211])).

tff(c_6889,plain,(
    k3_xboole_0('#skF_1','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_18,c_6795])).

tff(c_6891,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_6889])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n020.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.98/2.72  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.98/2.73  
% 6.98/2.73  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.98/2.73  %$ r2_hidden > r1_tarski > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 6.98/2.73  
% 6.98/2.73  %Foreground sorts:
% 6.98/2.73  
% 6.98/2.73  
% 6.98/2.73  %Background operators:
% 6.98/2.73  
% 6.98/2.73  
% 6.98/2.73  %Foreground operators:
% 6.98/2.73  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.98/2.73  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.98/2.73  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.98/2.73  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.98/2.73  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.98/2.73  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.98/2.73  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.98/2.73  tff('#skF_2', type, '#skF_2': $i).
% 6.98/2.73  tff('#skF_3', type, '#skF_3': $i).
% 6.98/2.73  tff('#skF_1', type, '#skF_1': $i).
% 6.98/2.73  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.98/2.73  tff('#skF_4', type, '#skF_4': $i).
% 6.98/2.73  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.98/2.73  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.98/2.73  
% 6.98/2.74  tff(f_54, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 6.98/2.74  tff(f_35, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.98/2.74  tff(f_45, axiom, (![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k3_xboole_0(k2_tarski(A, C), B) = k2_tarski(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 6.98/2.74  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.98/2.74  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.98/2.74  tff(f_29, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 6.98/2.74  tff(c_16, plain, (k3_xboole_0('#skF_1', '#skF_3')!=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.98/2.74  tff(c_18, plain, (r2_hidden('#skF_4', '#skF_1')), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.98/2.74  tff(c_8, plain, (![A_8]: (k2_tarski(A_8, A_8)=k1_tarski(A_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.98/2.74  tff(c_161, plain, (![A_30, C_31, B_32]: (k3_xboole_0(k2_tarski(A_30, C_31), B_32)=k2_tarski(A_30, C_31) | ~r2_hidden(C_31, B_32) | ~r2_hidden(A_30, B_32))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.98/2.74  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.98/2.74  tff(c_4607, plain, (![B_69, A_70, C_71]: (k3_xboole_0(B_69, k2_tarski(A_70, C_71))=k2_tarski(A_70, C_71) | ~r2_hidden(C_71, B_69) | ~r2_hidden(A_70, B_69))), inference(superposition, [status(thm), theory('equality')], [c_161, c_2])).
% 6.98/2.74  tff(c_4735, plain, (![B_69, A_8]: (k3_xboole_0(B_69, k1_tarski(A_8))=k2_tarski(A_8, A_8) | ~r2_hidden(A_8, B_69) | ~r2_hidden(A_8, B_69))), inference(superposition, [status(thm), theory('equality')], [c_8, c_4607])).
% 6.98/2.74  tff(c_6687, plain, (![B_84, A_85]: (k3_xboole_0(B_84, k1_tarski(A_85))=k1_tarski(A_85) | ~r2_hidden(A_85, B_84) | ~r2_hidden(A_85, B_84))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_4735])).
% 6.98/2.74  tff(c_20, plain, (k3_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_4')), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.98/2.74  tff(c_22, plain, (r1_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_54])).
% 6.98/2.74  tff(c_97, plain, (![A_22, B_23]: (k3_xboole_0(A_22, B_23)=A_22 | ~r1_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.98/2.74  tff(c_101, plain, (k3_xboole_0('#skF_1', '#skF_2')='#skF_1'), inference(resolution, [status(thm)], [c_22, c_97])).
% 6.98/2.74  tff(c_115, plain, (![A_27, B_28, C_29]: (k3_xboole_0(k3_xboole_0(A_27, B_28), C_29)=k3_xboole_0(A_27, k3_xboole_0(B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.98/2.74  tff(c_191, plain, (![C_33]: (k3_xboole_0('#skF_1', k3_xboole_0('#skF_2', C_33))=k3_xboole_0('#skF_1', C_33))), inference(superposition, [status(thm), theory('equality')], [c_101, c_115])).
% 6.98/2.74  tff(c_211, plain, (k3_xboole_0('#skF_1', k1_tarski('#skF_4'))=k3_xboole_0('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_20, c_191])).
% 6.98/2.74  tff(c_6795, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4') | ~r2_hidden('#skF_4', '#skF_1') | ~r2_hidden('#skF_4', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_6687, c_211])).
% 6.98/2.74  tff(c_6889, plain, (k3_xboole_0('#skF_1', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_18, c_6795])).
% 6.98/2.74  tff(c_6891, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_6889])).
% 6.98/2.74  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.98/2.74  
% 6.98/2.74  Inference rules
% 6.98/2.74  ----------------------
% 6.98/2.74  #Ref     : 0
% 6.98/2.74  #Sup     : 1748
% 6.98/2.74  #Fact    : 0
% 6.98/2.74  #Define  : 0
% 6.98/2.74  #Split   : 0
% 6.98/2.74  #Chain   : 0
% 6.98/2.74  #Close   : 0
% 6.98/2.74  
% 6.98/2.74  Ordering : KBO
% 6.98/2.74  
% 6.98/2.74  Simplification rules
% 6.98/2.74  ----------------------
% 6.98/2.74  #Subsume      : 278
% 6.98/2.74  #Demod        : 1440
% 6.98/2.74  #Tautology    : 432
% 6.98/2.74  #SimpNegUnit  : 1
% 6.98/2.74  #BackRed      : 1
% 6.98/2.74  
% 6.98/2.74  #Partial instantiations: 0
% 6.98/2.74  #Strategies tried      : 1
% 6.98/2.74  
% 6.98/2.74  Timing (in seconds)
% 6.98/2.74  ----------------------
% 6.98/2.74  Preprocessing        : 0.28
% 6.98/2.74  Parsing              : 0.16
% 6.98/2.74  CNF conversion       : 0.02
% 6.98/2.74  Main loop            : 1.69
% 6.98/2.74  Inferencing          : 0.34
% 6.98/2.74  Reduction            : 1.10
% 6.98/2.74  Demodulation         : 1.02
% 6.98/2.74  BG Simplification    : 0.06
% 6.98/2.74  Subsumption          : 0.15
% 6.98/2.74  Abstraction          : 0.09
% 6.98/2.74  MUC search           : 0.00
% 6.98/2.74  Cooper               : 0.00
% 6.98/2.74  Total                : 2.00
% 6.98/2.74  Index Insertion      : 0.00
% 6.98/2.74  Index Deletion       : 0.00
% 6.98/2.74  Index Matching       : 0.00
% 6.98/2.74  BG Taut test         : 0.00
%------------------------------------------------------------------------------

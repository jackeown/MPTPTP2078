%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:17 EST 2020

% Result     : Theorem 2.11s
% Output     : CNFRefutation 2.11s
% Verified   : 
% Statistics : Number of formulae       :   37 (  41 expanded)
%              Number of leaves         :   21 (  24 expanded)
%              Depth                    :    7
%              Number of atoms          :   36 (  42 expanded)
%              Number of equality atoms :   14 (  17 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_54,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_xboole_0(k1_tarski(A),B)
        | k3_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t58_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_91,plain,(
    ! [A_26,B_27] :
      ( r1_xboole_0(k1_tarski(A_26),B_27)
      | r2_hidden(A_26,B_27) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_38,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_3'),'#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_95,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(resolution,[status(thm)],[c_91,c_38])).

tff(c_22,plain,(
    ! [A_9,B_10] : k4_xboole_0(A_9,k4_xboole_0(A_9,B_10)) = k3_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_34,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(k1_tarski(A_19),B_20)
      | r2_hidden(A_19,B_20) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_101,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(A_30,B_31) = A_30
      | ~ r1_xboole_0(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_156,plain,(
    ! [A_49,B_50] :
      ( k4_xboole_0(k1_tarski(A_49),B_50) = k1_tarski(A_49)
      | r2_hidden(A_49,B_50) ) ),
    inference(resolution,[status(thm)],[c_34,c_101])).

tff(c_317,plain,(
    ! [A_68,B_69] :
      ( k3_xboole_0(k1_tarski(A_68),B_69) = k1_tarski(A_68)
      | r2_hidden(A_68,k4_xboole_0(k1_tarski(A_68),B_69)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_156])).

tff(c_6,plain,(
    ! [D_8,B_4,A_3] :
      ( ~ r2_hidden(D_8,B_4)
      | ~ r2_hidden(D_8,k4_xboole_0(A_3,B_4)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_348,plain,(
    ! [A_70,B_71] :
      ( ~ r2_hidden(A_70,B_71)
      | k3_xboole_0(k1_tarski(A_70),B_71) = k1_tarski(A_70) ) ),
    inference(resolution,[status(thm)],[c_317,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_388,plain,(
    ! [B_75,A_76] :
      ( k3_xboole_0(B_75,k1_tarski(A_76)) = k1_tarski(A_76)
      | ~ r2_hidden(A_76,B_75) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_348,c_2])).

tff(c_36,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),'#skF_4') != k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_39,plain,(
    k3_xboole_0('#skF_4',k1_tarski('#skF_3')) != k1_tarski('#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_36])).

tff(c_410,plain,(
    ~ r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_388,c_39])).

tff(c_436,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_95,c_410])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n012.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 09:40:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.11/1.28  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.28  
% 2.11/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.29  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 2.11/1.29  
% 2.11/1.29  %Foreground sorts:
% 2.11/1.29  
% 2.11/1.29  
% 2.11/1.29  %Background operators:
% 2.11/1.29  
% 2.11/1.29  
% 2.11/1.29  %Foreground operators:
% 2.11/1.29  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.11/1.29  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.11/1.29  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.11/1.29  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.11/1.29  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.11/1.29  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.11/1.29  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.11/1.29  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.11/1.29  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.11/1.29  tff('#skF_3', type, '#skF_3': $i).
% 2.11/1.29  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.11/1.29  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.11/1.29  tff('#skF_4', type, '#skF_4': $i).
% 2.11/1.29  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.11/1.29  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.11/1.29  
% 2.11/1.29  tff(f_54, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.11/1.29  tff(f_59, negated_conjecture, ~(![A, B]: (r1_xboole_0(k1_tarski(A), B) | (k3_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t58_zfmisc_1)).
% 2.11/1.29  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.11/1.29  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.11/1.29  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.11/1.29  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.11/1.29  tff(c_91, plain, (![A_26, B_27]: (r1_xboole_0(k1_tarski(A_26), B_27) | r2_hidden(A_26, B_27))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.11/1.29  tff(c_38, plain, (~r1_xboole_0(k1_tarski('#skF_3'), '#skF_4')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.11/1.29  tff(c_95, plain, (r2_hidden('#skF_3', '#skF_4')), inference(resolution, [status(thm)], [c_91, c_38])).
% 2.11/1.29  tff(c_22, plain, (![A_9, B_10]: (k4_xboole_0(A_9, k4_xboole_0(A_9, B_10))=k3_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.11/1.29  tff(c_34, plain, (![A_19, B_20]: (r1_xboole_0(k1_tarski(A_19), B_20) | r2_hidden(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.11/1.29  tff(c_101, plain, (![A_30, B_31]: (k4_xboole_0(A_30, B_31)=A_30 | ~r1_xboole_0(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.11/1.29  tff(c_156, plain, (![A_49, B_50]: (k4_xboole_0(k1_tarski(A_49), B_50)=k1_tarski(A_49) | r2_hidden(A_49, B_50))), inference(resolution, [status(thm)], [c_34, c_101])).
% 2.11/1.29  tff(c_317, plain, (![A_68, B_69]: (k3_xboole_0(k1_tarski(A_68), B_69)=k1_tarski(A_68) | r2_hidden(A_68, k4_xboole_0(k1_tarski(A_68), B_69)))), inference(superposition, [status(thm), theory('equality')], [c_22, c_156])).
% 2.11/1.29  tff(c_6, plain, (![D_8, B_4, A_3]: (~r2_hidden(D_8, B_4) | ~r2_hidden(D_8, k4_xboole_0(A_3, B_4)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.11/1.29  tff(c_348, plain, (![A_70, B_71]: (~r2_hidden(A_70, B_71) | k3_xboole_0(k1_tarski(A_70), B_71)=k1_tarski(A_70))), inference(resolution, [status(thm)], [c_317, c_6])).
% 2.11/1.29  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.11/1.29  tff(c_388, plain, (![B_75, A_76]: (k3_xboole_0(B_75, k1_tarski(A_76))=k1_tarski(A_76) | ~r2_hidden(A_76, B_75))), inference(superposition, [status(thm), theory('equality')], [c_348, c_2])).
% 2.11/1.29  tff(c_36, plain, (k3_xboole_0(k1_tarski('#skF_3'), '#skF_4')!=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.11/1.29  tff(c_39, plain, (k3_xboole_0('#skF_4', k1_tarski('#skF_3'))!=k1_tarski('#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_36])).
% 2.11/1.29  tff(c_410, plain, (~r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_388, c_39])).
% 2.11/1.29  tff(c_436, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_95, c_410])).
% 2.11/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.11/1.29  
% 2.11/1.29  Inference rules
% 2.11/1.29  ----------------------
% 2.11/1.29  #Ref     : 0
% 2.11/1.29  #Sup     : 102
% 2.11/1.29  #Fact    : 0
% 2.11/1.29  #Define  : 0
% 2.11/1.29  #Split   : 0
% 2.11/1.29  #Chain   : 0
% 2.11/1.29  #Close   : 0
% 2.11/1.30  
% 2.11/1.30  Ordering : KBO
% 2.11/1.30  
% 2.11/1.30  Simplification rules
% 2.11/1.30  ----------------------
% 2.11/1.30  #Subsume      : 6
% 2.11/1.30  #Demod        : 7
% 2.11/1.30  #Tautology    : 39
% 2.11/1.30  #SimpNegUnit  : 0
% 2.11/1.30  #BackRed      : 0
% 2.11/1.30  
% 2.11/1.30  #Partial instantiations: 0
% 2.11/1.30  #Strategies tried      : 1
% 2.11/1.30  
% 2.11/1.30  Timing (in seconds)
% 2.11/1.30  ----------------------
% 2.11/1.30  Preprocessing        : 0.29
% 2.11/1.30  Parsing              : 0.15
% 2.11/1.30  CNF conversion       : 0.02
% 2.11/1.30  Main loop            : 0.25
% 2.11/1.30  Inferencing          : 0.09
% 2.11/1.30  Reduction            : 0.08
% 2.11/1.30  Demodulation         : 0.06
% 2.11/1.30  BG Simplification    : 0.02
% 2.11/1.30  Subsumption          : 0.04
% 2.11/1.30  Abstraction          : 0.02
% 2.11/1.30  MUC search           : 0.00
% 2.11/1.30  Cooper               : 0.00
% 2.11/1.30  Total                : 0.57
% 2.11/1.30  Index Insertion      : 0.00
% 2.11/1.30  Index Deletion       : 0.00
% 2.11/1.30  Index Matching       : 0.00
% 2.11/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:52 EST 2020

% Result     : Theorem 2.69s
% Output     : CNFRefutation 2.83s
% Verified   : 
% Statistics : Number of formulae       :   45 (  65 expanded)
%              Number of leaves         :   28 (  36 expanded)
%              Depth                    :    9
%              Number of atoms          :   43 (  72 expanded)
%              Number of equality atoms :   20 (  40 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_89,negated_conjecture,(
    ~ ! [A,B,C] :
        ( A != B
       => k4_xboole_0(k2_xboole_0(C,k1_tarski(A)),k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C,k1_tarski(B)),k1_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_zfmisc_1)).

tff(f_69,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
    <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l33_zfmisc_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_58,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_74,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_58,plain,(
    ! [A_30,B_31] :
      ( k4_xboole_0(k1_tarski(A_30),B_31) = k1_tarski(A_30)
      | r2_hidden(A_30,B_31) ) ),
    inference(cnfTransformation,[status(thm)],[f_69])).

tff(c_46,plain,(
    ! [A_19,B_20] :
      ( r1_xboole_0(A_19,B_20)
      | k4_xboole_0(A_19,B_20) != A_19 ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_594,plain,(
    ! [C_112,B_113,A_114] :
      ( k4_xboole_0(k2_xboole_0(C_112,B_113),A_114) = k2_xboole_0(k4_xboole_0(C_112,A_114),B_113)
      | ~ r1_xboole_0(A_114,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_72,plain,(
    k4_xboole_0(k2_xboole_0('#skF_7',k1_tarski('#skF_5')),k1_tarski('#skF_6')) != k2_xboole_0(k4_xboole_0('#skF_7',k1_tarski('#skF_6')),k1_tarski('#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_75,plain,(
    k4_xboole_0(k2_xboole_0('#skF_7',k1_tarski('#skF_5')),k1_tarski('#skF_6')) != k2_xboole_0(k1_tarski('#skF_5'),k4_xboole_0('#skF_7',k1_tarski('#skF_6'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_72])).

tff(c_638,plain,
    ( k2_xboole_0(k4_xboole_0('#skF_7',k1_tarski('#skF_6')),k1_tarski('#skF_5')) != k2_xboole_0(k1_tarski('#skF_5'),k4_xboole_0('#skF_7',k1_tarski('#skF_6')))
    | ~ r1_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_594,c_75])).

tff(c_669,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_638])).

tff(c_676,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) != k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_46,c_669])).

tff(c_683,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_676])).

tff(c_465,plain,(
    ! [A_99,B_100,C_101] :
      ( r2_hidden(A_99,k4_xboole_0(B_100,k1_tarski(C_101)))
      | C_101 = A_99
      | ~ r2_hidden(A_99,B_100) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_24,plain,(
    ! [D_14,B_10,A_9] :
      ( ~ r2_hidden(D_14,B_10)
      | ~ r2_hidden(D_14,k4_xboole_0(A_9,B_10)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_504,plain,(
    ! [A_99,C_101,B_100] :
      ( ~ r2_hidden(A_99,k1_tarski(C_101))
      | C_101 = A_99
      | ~ r2_hidden(A_99,B_100) ) ),
    inference(resolution,[status(thm)],[c_465,c_24])).

tff(c_688,plain,(
    ! [B_100] :
      ( '#skF_5' = '#skF_6'
      | ~ r2_hidden('#skF_6',B_100) ) ),
    inference(resolution,[status(thm)],[c_683,c_504])).

tff(c_697,plain,(
    ! [B_100] : ~ r2_hidden('#skF_6',B_100) ),
    inference(negUnitSimplification,[status(thm)],[c_74,c_688])).

tff(c_703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_697,c_683])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:02:19 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.69/1.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.35  
% 2.69/1.35  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.69/1.36  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_1 > #skF_4 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3
% 2.69/1.36  
% 2.69/1.36  %Foreground sorts:
% 2.69/1.36  
% 2.69/1.36  
% 2.69/1.36  %Background operators:
% 2.69/1.36  
% 2.69/1.36  
% 2.69/1.36  %Foreground operators:
% 2.69/1.36  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.69/1.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.69/1.36  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.69/1.36  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.69/1.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.69/1.36  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 2.69/1.36  tff('#skF_7', type, '#skF_7': $i).
% 2.69/1.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.69/1.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.69/1.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.69/1.36  tff('#skF_5', type, '#skF_5': $i).
% 2.69/1.36  tff('#skF_6', type, '#skF_6': $i).
% 2.69/1.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.69/1.36  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.69/1.36  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.69/1.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.69/1.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.69/1.36  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 2.69/1.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.69/1.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.69/1.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.69/1.36  
% 2.83/1.37  tff(f_89, negated_conjecture, ~(![A, B, C]: (~(A = B) => (k4_xboole_0(k2_xboole_0(C, k1_tarski(A)), k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C, k1_tarski(B)), k1_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_zfmisc_1)).
% 2.83/1.37  tff(f_69, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l33_zfmisc_1)).
% 2.83/1.37  tff(f_54, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.83/1.37  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 2.83/1.37  tff(f_58, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_xboole_1)).
% 2.83/1.37  tff(f_78, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.83/1.37  tff(f_46, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.83/1.37  tff(c_74, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.83/1.37  tff(c_58, plain, (![A_30, B_31]: (k4_xboole_0(k1_tarski(A_30), B_31)=k1_tarski(A_30) | r2_hidden(A_30, B_31))), inference(cnfTransformation, [status(thm)], [f_69])).
% 2.83/1.37  tff(c_46, plain, (![A_19, B_20]: (r1_xboole_0(A_19, B_20) | k4_xboole_0(A_19, B_20)!=A_19)), inference(cnfTransformation, [status(thm)], [f_54])).
% 2.83/1.37  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.83/1.37  tff(c_594, plain, (![C_112, B_113, A_114]: (k4_xboole_0(k2_xboole_0(C_112, B_113), A_114)=k2_xboole_0(k4_xboole_0(C_112, A_114), B_113) | ~r1_xboole_0(A_114, B_113))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.83/1.37  tff(c_72, plain, (k4_xboole_0(k2_xboole_0('#skF_7', k1_tarski('#skF_5')), k1_tarski('#skF_6'))!=k2_xboole_0(k4_xboole_0('#skF_7', k1_tarski('#skF_6')), k1_tarski('#skF_5'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 2.83/1.37  tff(c_75, plain, (k4_xboole_0(k2_xboole_0('#skF_7', k1_tarski('#skF_5')), k1_tarski('#skF_6'))!=k2_xboole_0(k1_tarski('#skF_5'), k4_xboole_0('#skF_7', k1_tarski('#skF_6')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_72])).
% 2.83/1.37  tff(c_638, plain, (k2_xboole_0(k4_xboole_0('#skF_7', k1_tarski('#skF_6')), k1_tarski('#skF_5'))!=k2_xboole_0(k1_tarski('#skF_5'), k4_xboole_0('#skF_7', k1_tarski('#skF_6'))) | ~r1_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_594, c_75])).
% 2.83/1.37  tff(c_669, plain, (~r1_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_638])).
% 2.83/1.37  tff(c_676, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))!=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_46, c_669])).
% 2.83/1.37  tff(c_683, plain, (r2_hidden('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_676])).
% 2.83/1.37  tff(c_465, plain, (![A_99, B_100, C_101]: (r2_hidden(A_99, k4_xboole_0(B_100, k1_tarski(C_101))) | C_101=A_99 | ~r2_hidden(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.83/1.37  tff(c_24, plain, (![D_14, B_10, A_9]: (~r2_hidden(D_14, B_10) | ~r2_hidden(D_14, k4_xboole_0(A_9, B_10)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.83/1.37  tff(c_504, plain, (![A_99, C_101, B_100]: (~r2_hidden(A_99, k1_tarski(C_101)) | C_101=A_99 | ~r2_hidden(A_99, B_100))), inference(resolution, [status(thm)], [c_465, c_24])).
% 2.83/1.37  tff(c_688, plain, (![B_100]: ('#skF_5'='#skF_6' | ~r2_hidden('#skF_6', B_100))), inference(resolution, [status(thm)], [c_683, c_504])).
% 2.83/1.37  tff(c_697, plain, (![B_100]: (~r2_hidden('#skF_6', B_100))), inference(negUnitSimplification, [status(thm)], [c_74, c_688])).
% 2.83/1.37  tff(c_703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_697, c_683])).
% 2.83/1.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.83/1.37  
% 2.83/1.37  Inference rules
% 2.83/1.37  ----------------------
% 2.83/1.37  #Ref     : 0
% 2.83/1.37  #Sup     : 159
% 2.83/1.37  #Fact    : 0
% 2.83/1.37  #Define  : 0
% 2.83/1.37  #Split   : 1
% 2.83/1.37  #Chain   : 0
% 2.83/1.37  #Close   : 0
% 2.83/1.37  
% 2.83/1.37  Ordering : KBO
% 2.83/1.37  
% 2.83/1.37  Simplification rules
% 2.83/1.37  ----------------------
% 2.83/1.37  #Subsume      : 35
% 2.83/1.37  #Demod        : 18
% 2.83/1.37  #Tautology    : 62
% 2.83/1.37  #SimpNegUnit  : 4
% 2.83/1.37  #BackRed      : 3
% 2.83/1.37  
% 2.83/1.37  #Partial instantiations: 0
% 2.83/1.37  #Strategies tried      : 1
% 2.83/1.37  
% 2.83/1.37  Timing (in seconds)
% 2.83/1.37  ----------------------
% 2.83/1.37  Preprocessing        : 0.32
% 2.83/1.37  Parsing              : 0.16
% 2.83/1.37  CNF conversion       : 0.02
% 2.83/1.37  Main loop            : 0.30
% 2.83/1.37  Inferencing          : 0.10
% 2.83/1.37  Reduction            : 0.10
% 2.83/1.37  Demodulation         : 0.07
% 2.83/1.37  BG Simplification    : 0.02
% 2.83/1.37  Subsumption          : 0.07
% 2.83/1.37  Abstraction          : 0.01
% 2.83/1.37  MUC search           : 0.00
% 2.83/1.37  Cooper               : 0.00
% 2.83/1.37  Total                : 0.64
% 2.83/1.37  Index Insertion      : 0.00
% 2.83/1.37  Index Deletion       : 0.00
% 2.83/1.37  Index Matching       : 0.00
% 2.83/1.37  BG Taut test         : 0.00
%------------------------------------------------------------------------------

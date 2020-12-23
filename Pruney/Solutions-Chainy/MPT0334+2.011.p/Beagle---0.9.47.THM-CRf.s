%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:52 EST 2020

% Result     : Theorem 1.83s
% Output     : CNFRefutation 1.83s
% Verified   : 
% Statistics : Number of formulae       :   32 (  35 expanded)
%              Number of leaves         :   20 (  22 expanded)
%              Depth                    :    7
%              Number of atoms          :   25 (  29 expanded)
%              Number of equality atoms :   18 (  22 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_54,negated_conjecture,(
    ~ ! [A,B,C] :
        ( A != B
       => k4_xboole_0(k2_xboole_0(C,k1_tarski(A)),k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C,k1_tarski(B)),k1_tarski(A)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t147_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_xboole_0(A,B)
     => k2_xboole_0(k4_xboole_0(C,A),B) = k4_xboole_0(k2_xboole_0(C,B),A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t87_xboole_1)).

tff(c_24,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_20,plain,(
    ! [A_15,B_16] :
      ( k4_xboole_0(k1_tarski(A_15),k1_tarski(B_16)) = k1_tarski(A_15)
      | B_16 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_5,B_6] :
      ( r1_xboole_0(A_5,B_6)
      | k4_xboole_0(A_5,B_6) != A_5 ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_136,plain,(
    ! [C_34,B_35,A_36] :
      ( k4_xboole_0(k2_xboole_0(C_34,B_35),A_36) = k2_xboole_0(k4_xboole_0(C_34,A_36),B_35)
      | ~ r1_xboole_0(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_22,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k1_tarski('#skF_1')),k1_tarski('#skF_2')) != k2_xboole_0(k4_xboole_0('#skF_3',k1_tarski('#skF_2')),k1_tarski('#skF_1')) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_25,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k1_tarski('#skF_1')),k1_tarski('#skF_2')) != k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_3',k1_tarski('#skF_2'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_22])).

tff(c_142,plain,
    ( k2_xboole_0(k4_xboole_0('#skF_3',k1_tarski('#skF_2')),k1_tarski('#skF_1')) != k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_3',k1_tarski('#skF_2')))
    | ~ r1_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_25])).

tff(c_157,plain,(
    ~ r1_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_142])).

tff(c_163,plain,(
    k4_xboole_0(k1_tarski('#skF_2'),k1_tarski('#skF_1')) != k1_tarski('#skF_2') ),
    inference(resolution,[status(thm)],[c_8,c_157])).

tff(c_166,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_163])).

tff(c_170,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_24,c_166])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:59:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.83/1.16  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.16  
% 1.83/1.16  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.16  %$ r1_xboole_0 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.83/1.16  
% 1.83/1.16  %Foreground sorts:
% 1.83/1.16  
% 1.83/1.16  
% 1.83/1.16  %Background operators:
% 1.83/1.16  
% 1.83/1.16  
% 1.83/1.16  %Foreground operators:
% 1.83/1.16  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.83/1.16  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.83/1.16  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.83/1.16  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.83/1.16  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.83/1.16  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.83/1.16  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.83/1.16  tff('#skF_2', type, '#skF_2': $i).
% 1.83/1.16  tff('#skF_3', type, '#skF_3': $i).
% 1.83/1.16  tff('#skF_1', type, '#skF_1': $i).
% 1.83/1.16  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.83/1.16  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.83/1.16  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.83/1.16  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.83/1.16  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.83/1.16  
% 1.83/1.17  tff(f_54, negated_conjecture, ~(![A, B, C]: (~(A = B) => (k4_xboole_0(k2_xboole_0(C, k1_tarski(A)), k1_tarski(B)) = k2_xboole_0(k4_xboole_0(C, k1_tarski(B)), k1_tarski(A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t147_zfmisc_1)).
% 1.83/1.17  tff(f_48, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.83/1.17  tff(f_33, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.83/1.17  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.83/1.17  tff(f_37, axiom, (![A, B, C]: (r1_xboole_0(A, B) => (k2_xboole_0(k4_xboole_0(C, A), B) = k4_xboole_0(k2_xboole_0(C, B), A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t87_xboole_1)).
% 1.83/1.17  tff(c_24, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.83/1.17  tff(c_20, plain, (![A_15, B_16]: (k4_xboole_0(k1_tarski(A_15), k1_tarski(B_16))=k1_tarski(A_15) | B_16=A_15)), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.83/1.17  tff(c_8, plain, (![A_5, B_6]: (r1_xboole_0(A_5, B_6) | k4_xboole_0(A_5, B_6)!=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.83/1.17  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.83/1.17  tff(c_136, plain, (![C_34, B_35, A_36]: (k4_xboole_0(k2_xboole_0(C_34, B_35), A_36)=k2_xboole_0(k4_xboole_0(C_34, A_36), B_35) | ~r1_xboole_0(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_37])).
% 1.83/1.17  tff(c_22, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k1_tarski('#skF_1')), k1_tarski('#skF_2'))!=k2_xboole_0(k4_xboole_0('#skF_3', k1_tarski('#skF_2')), k1_tarski('#skF_1'))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.83/1.17  tff(c_25, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k1_tarski('#skF_1')), k1_tarski('#skF_2'))!=k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_3', k1_tarski('#skF_2')))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_22])).
% 1.83/1.17  tff(c_142, plain, (k2_xboole_0(k4_xboole_0('#skF_3', k1_tarski('#skF_2')), k1_tarski('#skF_1'))!=k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_3', k1_tarski('#skF_2'))) | ~r1_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_136, c_25])).
% 1.83/1.17  tff(c_157, plain, (~r1_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_142])).
% 1.83/1.17  tff(c_163, plain, (k4_xboole_0(k1_tarski('#skF_2'), k1_tarski('#skF_1'))!=k1_tarski('#skF_2')), inference(resolution, [status(thm)], [c_8, c_157])).
% 1.83/1.17  tff(c_166, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_20, c_163])).
% 1.83/1.17  tff(c_170, plain, $false, inference(negUnitSimplification, [status(thm)], [c_24, c_166])).
% 1.83/1.17  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.83/1.17  
% 1.83/1.17  Inference rules
% 1.83/1.17  ----------------------
% 1.83/1.17  #Ref     : 0
% 1.83/1.17  #Sup     : 33
% 1.83/1.17  #Fact    : 0
% 1.83/1.17  #Define  : 0
% 1.83/1.17  #Split   : 0
% 1.83/1.17  #Chain   : 0
% 1.83/1.17  #Close   : 0
% 1.83/1.17  
% 1.83/1.17  Ordering : KBO
% 1.83/1.17  
% 1.83/1.17  Simplification rules
% 1.83/1.17  ----------------------
% 1.83/1.17  #Subsume      : 2
% 1.83/1.17  #Demod        : 3
% 1.83/1.17  #Tautology    : 24
% 1.83/1.17  #SimpNegUnit  : 1
% 1.83/1.17  #BackRed      : 0
% 1.83/1.17  
% 1.83/1.17  #Partial instantiations: 0
% 1.83/1.17  #Strategies tried      : 1
% 1.83/1.17  
% 1.83/1.17  Timing (in seconds)
% 1.83/1.17  ----------------------
% 1.83/1.17  Preprocessing        : 0.29
% 1.83/1.17  Parsing              : 0.15
% 1.83/1.17  CNF conversion       : 0.02
% 1.83/1.17  Main loop            : 0.13
% 1.83/1.17  Inferencing          : 0.05
% 1.83/1.17  Reduction            : 0.05
% 1.83/1.17  Demodulation         : 0.04
% 1.83/1.18  BG Simplification    : 0.01
% 1.83/1.18  Subsumption          : 0.02
% 1.83/1.18  Abstraction          : 0.01
% 1.83/1.18  MUC search           : 0.00
% 1.83/1.18  Cooper               : 0.00
% 1.83/1.18  Total                : 0.44
% 1.83/1.18  Index Insertion      : 0.00
% 1.83/1.18  Index Deletion       : 0.00
% 1.83/1.18  Index Matching       : 0.00
% 1.83/1.18  BG Taut test         : 0.00
%------------------------------------------------------------------------------

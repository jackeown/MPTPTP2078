%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:27 EST 2020

% Result     : Theorem 1.92s
% Output     : CNFRefutation 1.92s
% Verified   : 
% Statistics : Number of formulae       :   39 (  51 expanded)
%              Number of leaves         :   23 (  28 expanded)
%              Depth                    :    6
%              Number of atoms          :   30 (  46 expanded)
%              Number of equality atoms :   17 (  33 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( k2_xboole_0(A,B) = k1_xboole_0
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t15_xboole_1)).

tff(f_33,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t65_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),B)
        & r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l24_zfmisc_1)).

tff(f_44,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_42,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_61,plain,(
    ! [B_29,A_30] : k2_xboole_0(B_29,A_30) = k2_xboole_0(A_30,B_29) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_36,plain,(
    k2_xboole_0(k1_tarski('#skF_3'),'#skF_4') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_76,plain,(
    k2_xboole_0('#skF_4',k1_tarski('#skF_3')) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_61,c_36])).

tff(c_113,plain,(
    ! [A_31,B_32] :
      ( k1_xboole_0 = A_31
      | k2_xboole_0(A_31,B_32) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_126,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_113])).

tff(c_6,plain,(
    ! [A_5] : r1_xboole_0(A_5,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_131,plain,(
    ! [A_5] : r1_xboole_0(A_5,'#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_6])).

tff(c_215,plain,(
    ! [A_41,B_42] :
      ( ~ r2_hidden(A_41,B_42)
      | ~ r1_xboole_0(k1_tarski(A_41),B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_223,plain,(
    ! [A_41] : ~ r2_hidden(A_41,'#skF_4') ),
    inference(resolution,[status(thm)],[c_131,c_215])).

tff(c_127,plain,(
    k1_tarski('#skF_3') = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_113])).

tff(c_136,plain,(
    k1_tarski('#skF_3') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_126,c_127])).

tff(c_26,plain,(
    ! [A_12] : k2_tarski(A_12,A_12) = k1_tarski(A_12) ),
    inference(cnfTransformation,[status(thm)],[f_44])).

tff(c_51,plain,(
    ! [D_24,B_25] : r2_hidden(D_24,k2_tarski(D_24,B_25)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_54,plain,(
    ! [A_12] : r2_hidden(A_12,k1_tarski(A_12)) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_51])).

tff(c_140,plain,(
    r2_hidden('#skF_3','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_54])).

tff(c_225,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_223,c_140])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n019.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 10:42:22 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.92/1.20  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.20  
% 1.92/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.20  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_3 > #skF_2 > #skF_4
% 1.92/1.20  
% 1.92/1.20  %Foreground sorts:
% 1.92/1.20  
% 1.92/1.20  
% 1.92/1.20  %Background operators:
% 1.92/1.20  
% 1.92/1.20  
% 1.92/1.20  %Foreground operators:
% 1.92/1.20  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 1.92/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.92/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.92/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.92/1.20  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.92/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.92/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.92/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.92/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.92/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.92/1.20  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 1.92/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.92/1.20  tff(k3_tarski, type, k3_tarski: $i > $i).
% 1.92/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.92/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.92/1.20  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.92/1.20  
% 1.92/1.21  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 1.92/1.21  tff(f_59, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 1.92/1.21  tff(f_31, axiom, (![A, B]: ((k2_xboole_0(A, B) = k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t15_xboole_1)).
% 1.92/1.21  tff(f_33, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t65_xboole_1)).
% 1.92/1.21  tff(f_53, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), B) & r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l24_zfmisc_1)).
% 1.92/1.21  tff(f_44, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 1.92/1.21  tff(f_42, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 1.92/1.21  tff(c_61, plain, (![B_29, A_30]: (k2_xboole_0(B_29, A_30)=k2_xboole_0(A_30, B_29))), inference(cnfTransformation, [status(thm)], [f_27])).
% 1.92/1.21  tff(c_36, plain, (k2_xboole_0(k1_tarski('#skF_3'), '#skF_4')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_59])).
% 1.92/1.21  tff(c_76, plain, (k2_xboole_0('#skF_4', k1_tarski('#skF_3'))=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_61, c_36])).
% 1.92/1.21  tff(c_113, plain, (![A_31, B_32]: (k1_xboole_0=A_31 | k2_xboole_0(A_31, B_32)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.92/1.21  tff(c_126, plain, (k1_xboole_0='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_76, c_113])).
% 1.92/1.21  tff(c_6, plain, (![A_5]: (r1_xboole_0(A_5, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.92/1.21  tff(c_131, plain, (![A_5]: (r1_xboole_0(A_5, '#skF_4'))), inference(demodulation, [status(thm), theory('equality')], [c_126, c_6])).
% 1.92/1.21  tff(c_215, plain, (![A_41, B_42]: (~r2_hidden(A_41, B_42) | ~r1_xboole_0(k1_tarski(A_41), B_42))), inference(cnfTransformation, [status(thm)], [f_53])).
% 1.92/1.21  tff(c_223, plain, (![A_41]: (~r2_hidden(A_41, '#skF_4'))), inference(resolution, [status(thm)], [c_131, c_215])).
% 1.92/1.21  tff(c_127, plain, (k1_tarski('#skF_3')=k1_xboole_0), inference(superposition, [status(thm), theory('equality')], [c_36, c_113])).
% 1.92/1.21  tff(c_136, plain, (k1_tarski('#skF_3')='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_126, c_127])).
% 1.92/1.21  tff(c_26, plain, (![A_12]: (k2_tarski(A_12, A_12)=k1_tarski(A_12))), inference(cnfTransformation, [status(thm)], [f_44])).
% 1.92/1.21  tff(c_51, plain, (![D_24, B_25]: (r2_hidden(D_24, k2_tarski(D_24, B_25)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 1.92/1.21  tff(c_54, plain, (![A_12]: (r2_hidden(A_12, k1_tarski(A_12)))), inference(superposition, [status(thm), theory('equality')], [c_26, c_51])).
% 1.92/1.21  tff(c_140, plain, (r2_hidden('#skF_3', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_136, c_54])).
% 1.92/1.21  tff(c_225, plain, $false, inference(negUnitSimplification, [status(thm)], [c_223, c_140])).
% 1.92/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.92/1.21  
% 1.92/1.21  Inference rules
% 1.92/1.21  ----------------------
% 1.92/1.21  #Ref     : 0
% 1.92/1.21  #Sup     : 50
% 1.92/1.21  #Fact    : 0
% 1.92/1.21  #Define  : 0
% 1.92/1.21  #Split   : 1
% 1.92/1.21  #Chain   : 0
% 1.92/1.21  #Close   : 0
% 1.92/1.21  
% 1.92/1.21  Ordering : KBO
% 1.92/1.21  
% 1.92/1.21  Simplification rules
% 1.92/1.21  ----------------------
% 1.92/1.21  #Subsume      : 3
% 1.92/1.21  #Demod        : 17
% 1.92/1.21  #Tautology    : 34
% 1.92/1.21  #SimpNegUnit  : 1
% 1.92/1.21  #BackRed      : 5
% 1.92/1.21  
% 1.92/1.21  #Partial instantiations: 0
% 1.92/1.21  #Strategies tried      : 1
% 1.92/1.21  
% 1.92/1.21  Timing (in seconds)
% 1.92/1.21  ----------------------
% 1.92/1.21  Preprocessing        : 0.30
% 1.92/1.21  Parsing              : 0.16
% 1.92/1.21  CNF conversion       : 0.02
% 1.92/1.21  Main loop            : 0.15
% 1.92/1.21  Inferencing          : 0.04
% 1.92/1.21  Reduction            : 0.05
% 1.92/1.21  Demodulation         : 0.04
% 1.92/1.21  BG Simplification    : 0.01
% 1.92/1.21  Subsumption          : 0.03
% 1.92/1.21  Abstraction          : 0.01
% 1.92/1.21  MUC search           : 0.00
% 1.92/1.21  Cooper               : 0.00
% 1.92/1.21  Total                : 0.48
% 1.92/1.21  Index Insertion      : 0.00
% 1.92/1.21  Index Deletion       : 0.00
% 1.92/1.22  Index Matching       : 0.00
% 1.92/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------

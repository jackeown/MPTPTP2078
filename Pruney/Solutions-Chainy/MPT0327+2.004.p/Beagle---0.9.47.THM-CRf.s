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
% DateTime   : Thu Dec  3 09:54:31 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   47 (  57 expanded)
%              Number of leaves         :   26 (  31 expanded)
%              Depth                    :    7
%              Number of atoms          :   41 (  52 expanded)
%              Number of equality atoms :   24 (  34 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1

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

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( r2_hidden(A,B)
       => k2_xboole_0(k4_xboole_0(B,k1_tarski(A)),k1_tarski(A)) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t140_zfmisc_1)).

tff(f_41,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_49,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(c_32,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_14,plain,(
    ! [A_13] : k2_tarski(A_13,A_13) = k1_tarski(A_13) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_349,plain,(
    ! [A_69,B_70,C_71] :
      ( r1_tarski(k2_tarski(A_69,B_70),C_71)
      | ~ r2_hidden(B_70,C_71)
      | ~ r2_hidden(A_69,C_71) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_371,plain,(
    ! [A_72,C_73] :
      ( r1_tarski(k1_tarski(A_72),C_73)
      | ~ r2_hidden(A_72,C_73)
      | ~ r2_hidden(A_72,C_73) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_349])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k3_xboole_0(A_7,B_8) = A_7
      | ~ r1_tarski(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_380,plain,(
    ! [A_74,C_75] :
      ( k3_xboole_0(k1_tarski(A_74),C_75) = k1_tarski(A_74)
      | ~ r2_hidden(A_74,C_75) ) ),
    inference(resolution,[status(thm)],[c_371,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_108,plain,(
    ! [A_33,B_34] : k2_xboole_0(A_33,k3_xboole_0(A_33,B_34)) = A_33 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_117,plain,(
    ! [A_1,B_2] : k2_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = A_1 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_108])).

tff(c_416,plain,(
    ! [C_76,A_77] :
      ( k2_xboole_0(C_76,k1_tarski(A_77)) = C_76
      | ~ r2_hidden(A_77,C_76) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_380,c_117])).

tff(c_12,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_152,plain,(
    ! [A_39,B_40] : k3_tarski(k2_tarski(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_196,plain,(
    ! [B_44,A_45] : k3_tarski(k2_tarski(B_44,A_45)) = k2_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_152])).

tff(c_22,plain,(
    ! [A_23,B_24] : k3_tarski(k2_tarski(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_202,plain,(
    ! [B_44,A_45] : k2_xboole_0(B_44,A_45) = k2_xboole_0(A_45,B_44) ),
    inference(superposition,[status(thm),theory(equality)],[c_196,c_22])).

tff(c_10,plain,(
    ! [A_9,B_10] : k2_xboole_0(A_9,k4_xboole_0(B_10,A_9)) = k2_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_30,plain,(
    k2_xboole_0(k4_xboole_0('#skF_2',k1_tarski('#skF_1')),k1_tarski('#skF_1')) != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_222,plain,(
    k2_xboole_0(k1_tarski('#skF_1'),k4_xboole_0('#skF_2',k1_tarski('#skF_1'))) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_30])).

tff(c_277,plain,(
    k2_xboole_0('#skF_2',k1_tarski('#skF_1')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_10,c_222])).

tff(c_422,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_416,c_277])).

tff(c_452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_32,c_422])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.13/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n005.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 09:21:02 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.24  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.24  
% 2.19/1.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.24  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > #skF_2 > #skF_1
% 2.19/1.24  
% 2.19/1.24  %Foreground sorts:
% 2.19/1.24  
% 2.19/1.24  
% 2.19/1.24  %Background operators:
% 2.19/1.24  
% 2.19/1.24  
% 2.19/1.24  %Foreground operators:
% 2.19/1.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.19/1.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.19/1.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.19/1.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.24  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.24  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 2.19/1.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.19/1.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.19/1.24  
% 2.19/1.25  tff(f_60, negated_conjecture, ~(![A, B]: (r2_hidden(A, B) => (k2_xboole_0(k4_xboole_0(B, k1_tarski(A)), k1_tarski(A)) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t140_zfmisc_1)).
% 2.19/1.25  tff(f_41, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.19/1.25  tff(f_55, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 2.19/1.25  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.19/1.25  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 2.19/1.25  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 2.19/1.25  tff(f_39, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.19/1.25  tff(f_49, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 2.19/1.25  tff(f_37, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 2.19/1.25  tff(c_32, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.19/1.25  tff(c_14, plain, (![A_13]: (k2_tarski(A_13, A_13)=k1_tarski(A_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.19/1.25  tff(c_349, plain, (![A_69, B_70, C_71]: (r1_tarski(k2_tarski(A_69, B_70), C_71) | ~r2_hidden(B_70, C_71) | ~r2_hidden(A_69, C_71))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.19/1.25  tff(c_371, plain, (![A_72, C_73]: (r1_tarski(k1_tarski(A_72), C_73) | ~r2_hidden(A_72, C_73) | ~r2_hidden(A_72, C_73))), inference(superposition, [status(thm), theory('equality')], [c_14, c_349])).
% 2.19/1.25  tff(c_8, plain, (![A_7, B_8]: (k3_xboole_0(A_7, B_8)=A_7 | ~r1_tarski(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.19/1.25  tff(c_380, plain, (![A_74, C_75]: (k3_xboole_0(k1_tarski(A_74), C_75)=k1_tarski(A_74) | ~r2_hidden(A_74, C_75))), inference(resolution, [status(thm)], [c_371, c_8])).
% 2.19/1.25  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.19/1.25  tff(c_108, plain, (![A_33, B_34]: (k2_xboole_0(A_33, k3_xboole_0(A_33, B_34))=A_33)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.25  tff(c_117, plain, (![A_1, B_2]: (k2_xboole_0(A_1, k3_xboole_0(B_2, A_1))=A_1)), inference(superposition, [status(thm), theory('equality')], [c_2, c_108])).
% 2.19/1.25  tff(c_416, plain, (![C_76, A_77]: (k2_xboole_0(C_76, k1_tarski(A_77))=C_76 | ~r2_hidden(A_77, C_76))), inference(superposition, [status(thm), theory('equality')], [c_380, c_117])).
% 2.19/1.25  tff(c_12, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.19/1.25  tff(c_152, plain, (![A_39, B_40]: (k3_tarski(k2_tarski(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.19/1.25  tff(c_196, plain, (![B_44, A_45]: (k3_tarski(k2_tarski(B_44, A_45))=k2_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_12, c_152])).
% 2.19/1.25  tff(c_22, plain, (![A_23, B_24]: (k3_tarski(k2_tarski(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.19/1.25  tff(c_202, plain, (![B_44, A_45]: (k2_xboole_0(B_44, A_45)=k2_xboole_0(A_45, B_44))), inference(superposition, [status(thm), theory('equality')], [c_196, c_22])).
% 2.19/1.25  tff(c_10, plain, (![A_9, B_10]: (k2_xboole_0(A_9, k4_xboole_0(B_10, A_9))=k2_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.25  tff(c_30, plain, (k2_xboole_0(k4_xboole_0('#skF_2', k1_tarski('#skF_1')), k1_tarski('#skF_1'))!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_60])).
% 2.19/1.25  tff(c_222, plain, (k2_xboole_0(k1_tarski('#skF_1'), k4_xboole_0('#skF_2', k1_tarski('#skF_1')))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_202, c_30])).
% 2.19/1.25  tff(c_277, plain, (k2_xboole_0('#skF_2', k1_tarski('#skF_1'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_202, c_10, c_222])).
% 2.19/1.25  tff(c_422, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_416, c_277])).
% 2.19/1.25  tff(c_452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_32, c_422])).
% 2.19/1.25  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.19/1.25  
% 2.19/1.25  Inference rules
% 2.19/1.25  ----------------------
% 2.19/1.25  #Ref     : 0
% 2.19/1.25  #Sup     : 103
% 2.19/1.25  #Fact    : 0
% 2.19/1.25  #Define  : 0
% 2.19/1.25  #Split   : 0
% 2.19/1.25  #Chain   : 0
% 2.19/1.25  #Close   : 0
% 2.19/1.25  
% 2.19/1.25  Ordering : KBO
% 2.19/1.25  
% 2.19/1.25  Simplification rules
% 2.19/1.25  ----------------------
% 2.19/1.25  #Subsume      : 9
% 2.19/1.25  #Demod        : 14
% 2.19/1.25  #Tautology    : 69
% 2.19/1.25  #SimpNegUnit  : 0
% 2.19/1.25  #BackRed      : 1
% 2.19/1.25  
% 2.19/1.25  #Partial instantiations: 0
% 2.19/1.25  #Strategies tried      : 1
% 2.19/1.25  
% 2.19/1.25  Timing (in seconds)
% 2.19/1.25  ----------------------
% 2.19/1.26  Preprocessing        : 0.30
% 2.19/1.26  Parsing              : 0.16
% 2.19/1.26  CNF conversion       : 0.02
% 2.19/1.26  Main loop            : 0.21
% 2.19/1.26  Inferencing          : 0.09
% 2.19/1.26  Reduction            : 0.07
% 2.19/1.26  Demodulation         : 0.06
% 2.19/1.26  BG Simplification    : 0.01
% 2.19/1.26  Subsumption          : 0.03
% 2.19/1.26  Abstraction          : 0.01
% 2.19/1.26  MUC search           : 0.00
% 2.19/1.26  Cooper               : 0.00
% 2.19/1.26  Total                : 0.54
% 2.19/1.26  Index Insertion      : 0.00
% 2.19/1.26  Index Deletion       : 0.00
% 2.19/1.26  Index Matching       : 0.00
% 2.19/1.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------

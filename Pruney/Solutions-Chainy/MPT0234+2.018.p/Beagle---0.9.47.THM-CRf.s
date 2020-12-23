%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:43 EST 2020

% Result     : Theorem 1.55s
% Output     : CNFRefutation 1.55s
% Verified   : 
% Statistics : Number of formulae       :   30 (  31 expanded)
%              Number of leaves         :   18 (  19 expanded)
%              Depth                    :    6
%              Number of atoms          :   26 (  28 expanded)
%              Number of equality atoms :   21 (  23 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_46,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_40,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(c_16,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_10,plain,(
    ! [A_6,B_7] : k2_xboole_0(k1_tarski(A_6),k1_tarski(B_7)) = k2_tarski(A_6,B_7) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6,plain,(
    ! [A_3] : k5_xboole_0(A_3,k1_xboole_0) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_32,plain,(
    ! [A_15,B_16] :
      ( r1_xboole_0(k1_tarski(A_15),k1_tarski(B_16))
      | B_16 = A_15 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_2,plain,(
    ! [A_1,B_2] :
      ( k3_xboole_0(A_1,B_2) = k1_xboole_0
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_36,plain,(
    ! [A_15,B_16] :
      ( k3_xboole_0(k1_tarski(A_15),k1_tarski(B_16)) = k1_xboole_0
      | B_16 = A_15 ) ),
    inference(resolution,[status(thm)],[c_32,c_2])).

tff(c_57,plain,(
    ! [A_21,B_22] : k5_xboole_0(k5_xboole_0(A_21,B_22),k3_xboole_0(A_21,B_22)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_72,plain,(
    ! [A_15,B_16] :
      ( k5_xboole_0(k5_xboole_0(k1_tarski(A_15),k1_tarski(B_16)),k1_xboole_0) = k2_xboole_0(k1_tarski(A_15),k1_tarski(B_16))
      | B_16 = A_15 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_36,c_57])).

tff(c_91,plain,(
    ! [A_24,B_25] :
      ( k5_xboole_0(k1_tarski(A_24),k1_tarski(B_25)) = k2_tarski(A_24,B_25)
      | B_25 = A_24 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_6,c_72])).

tff(c_14,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_100,plain,(
    '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_91,c_14])).

tff(c_109,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_16,c_100])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n017.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:13:01 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.55/1.13  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.13  
% 1.55/1.13  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.13  %$ r1_xboole_0 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.55/1.13  
% 1.55/1.13  %Foreground sorts:
% 1.55/1.13  
% 1.55/1.13  
% 1.55/1.13  %Background operators:
% 1.55/1.13  
% 1.55/1.13  
% 1.55/1.13  %Foreground operators:
% 1.55/1.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.55/1.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.55/1.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.55/1.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.55/1.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.55/1.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.55/1.13  tff('#skF_2', type, '#skF_2': $i).
% 1.55/1.13  tff('#skF_1', type, '#skF_1': $i).
% 1.55/1.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.55/1.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.55/1.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.55/1.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.55/1.13  
% 1.55/1.14  tff(f_46, negated_conjecture, ~(![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 1.55/1.14  tff(f_35, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.55/1.14  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 1.55/1.14  tff(f_40, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.55/1.14  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.55/1.14  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 1.55/1.14  tff(c_16, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.55/1.14  tff(c_10, plain, (![A_6, B_7]: (k2_xboole_0(k1_tarski(A_6), k1_tarski(B_7))=k2_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 1.55/1.14  tff(c_6, plain, (![A_3]: (k5_xboole_0(A_3, k1_xboole_0)=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.55/1.14  tff(c_32, plain, (![A_15, B_16]: (r1_xboole_0(k1_tarski(A_15), k1_tarski(B_16)) | B_16=A_15)), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.55/1.14  tff(c_2, plain, (![A_1, B_2]: (k3_xboole_0(A_1, B_2)=k1_xboole_0 | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.55/1.14  tff(c_36, plain, (![A_15, B_16]: (k3_xboole_0(k1_tarski(A_15), k1_tarski(B_16))=k1_xboole_0 | B_16=A_15)), inference(resolution, [status(thm)], [c_32, c_2])).
% 1.55/1.14  tff(c_57, plain, (![A_21, B_22]: (k5_xboole_0(k5_xboole_0(A_21, B_22), k3_xboole_0(A_21, B_22))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.55/1.14  tff(c_72, plain, (![A_15, B_16]: (k5_xboole_0(k5_xboole_0(k1_tarski(A_15), k1_tarski(B_16)), k1_xboole_0)=k2_xboole_0(k1_tarski(A_15), k1_tarski(B_16)) | B_16=A_15)), inference(superposition, [status(thm), theory('equality')], [c_36, c_57])).
% 1.55/1.14  tff(c_91, plain, (![A_24, B_25]: (k5_xboole_0(k1_tarski(A_24), k1_tarski(B_25))=k2_tarski(A_24, B_25) | B_25=A_24)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_6, c_72])).
% 1.55/1.14  tff(c_14, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_46])).
% 1.55/1.14  tff(c_100, plain, ('#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_91, c_14])).
% 1.55/1.14  tff(c_109, plain, $false, inference(negUnitSimplification, [status(thm)], [c_16, c_100])).
% 1.55/1.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.55/1.14  
% 1.55/1.14  Inference rules
% 1.55/1.14  ----------------------
% 1.55/1.14  #Ref     : 0
% 1.55/1.14  #Sup     : 21
% 1.55/1.14  #Fact    : 0
% 1.55/1.14  #Define  : 0
% 1.55/1.14  #Split   : 0
% 1.55/1.14  #Chain   : 0
% 1.55/1.14  #Close   : 0
% 1.55/1.14  
% 1.55/1.14  Ordering : KBO
% 1.55/1.14  
% 1.55/1.14  Simplification rules
% 1.55/1.14  ----------------------
% 1.55/1.14  #Subsume      : 0
% 1.55/1.14  #Demod        : 3
% 1.55/1.14  #Tautology    : 12
% 1.55/1.14  #SimpNegUnit  : 1
% 1.55/1.14  #BackRed      : 0
% 1.55/1.14  
% 1.55/1.14  #Partial instantiations: 0
% 1.55/1.14  #Strategies tried      : 1
% 1.55/1.14  
% 1.55/1.14  Timing (in seconds)
% 1.55/1.14  ----------------------
% 1.55/1.14  Preprocessing        : 0.26
% 1.55/1.14  Parsing              : 0.14
% 1.55/1.14  CNF conversion       : 0.01
% 1.55/1.14  Main loop            : 0.10
% 1.55/1.14  Inferencing          : 0.04
% 1.55/1.14  Reduction            : 0.03
% 1.55/1.15  Demodulation         : 0.02
% 1.55/1.15  BG Simplification    : 0.01
% 1.55/1.15  Subsumption          : 0.01
% 1.55/1.15  Abstraction          : 0.01
% 1.55/1.15  MUC search           : 0.00
% 1.55/1.15  Cooper               : 0.00
% 1.55/1.15  Total                : 0.37
% 1.55/1.15  Index Insertion      : 0.00
% 1.55/1.15  Index Deletion       : 0.00
% 1.55/1.15  Index Matching       : 0.00
% 1.55/1.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

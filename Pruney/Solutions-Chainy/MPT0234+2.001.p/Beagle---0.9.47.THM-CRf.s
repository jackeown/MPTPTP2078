%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:41 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   36 (  43 expanded)
%              Number of leaves         :   19 (  23 expanded)
%              Depth                    :    8
%              Number of atoms          :   32 (  40 expanded)
%              Number of equality atoms :   31 (  39 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    5 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1

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

tff(f_52,negated_conjecture,(
    ~ ! [A,B] :
        ( A != B
       => k5_xboole_0(k1_tarski(A),k1_tarski(B)) = k2_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t29_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_41,axiom,(
    ! [A,B] : k3_xboole_0(k1_tarski(A),k2_tarski(A,B)) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t19_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_46,axiom,(
    ! [A,B] :
      ( A != B
     => k4_xboole_0(k2_tarski(A,B),k1_tarski(B)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t23_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(c_22,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_12,plain,(
    ! [B_12,A_11] : k2_tarski(B_12,A_11) = k2_tarski(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_16,plain,(
    ! [A_14,B_15] : k3_xboole_0(k1_tarski(A_14),k2_tarski(A_14,B_15)) = k1_tarski(A_14) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_367,plain,(
    ! [A_43,B_44] :
      ( k4_xboole_0(k2_tarski(A_43,B_44),k1_tarski(B_44)) = k1_tarski(A_43)
      | B_44 = A_43 ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_379,plain,(
    ! [B_12,A_11] :
      ( k4_xboole_0(k2_tarski(B_12,A_11),k1_tarski(B_12)) = k1_tarski(A_11)
      | B_12 = A_11 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_367])).

tff(c_6,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k3_xboole_0(A_3,B_4)) = k4_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_304,plain,(
    ! [A_39,B_40] : k5_xboole_0(k5_xboole_0(A_39,B_40),k3_xboole_0(A_39,B_40)) = k2_xboole_0(A_39,B_40) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_331,plain,(
    ! [A_3,B_4] : k5_xboole_0(k4_xboole_0(A_3,B_4),k3_xboole_0(A_3,k3_xboole_0(A_3,B_4))) = k2_xboole_0(A_3,k3_xboole_0(A_3,B_4)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_304])).

tff(c_628,plain,(
    ! [A_57,B_58] : k5_xboole_0(k4_xboole_0(A_57,B_58),k3_xboole_0(A_57,k3_xboole_0(A_57,B_58))) = A_57 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_331])).

tff(c_646,plain,(
    ! [A_11,B_12] :
      ( k5_xboole_0(k1_tarski(A_11),k3_xboole_0(k2_tarski(B_12,A_11),k3_xboole_0(k2_tarski(B_12,A_11),k1_tarski(B_12)))) = k2_tarski(B_12,A_11)
      | B_12 = A_11 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_379,c_628])).

tff(c_870,plain,(
    ! [A_68,B_69] :
      ( k5_xboole_0(k1_tarski(A_68),k1_tarski(B_69)) = k2_tarski(B_69,A_68)
      | B_69 = A_68 ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_2,c_16,c_2,c_646])).

tff(c_20,plain,(
    k5_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) != k2_tarski('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_886,plain,
    ( k2_tarski('#skF_2','#skF_1') != k2_tarski('#skF_1','#skF_2')
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_870,c_20])).

tff(c_897,plain,(
    '#skF_2' = '#skF_1' ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_886])).

tff(c_899,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_22,c_897])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n023.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:21:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.90  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.90  
% 3.15/1.90  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.91  %$ k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_1
% 3.15/1.91  
% 3.15/1.91  %Foreground sorts:
% 3.15/1.91  
% 3.15/1.91  
% 3.15/1.91  %Background operators:
% 3.15/1.91  
% 3.15/1.91  
% 3.15/1.91  %Foreground operators:
% 3.15/1.91  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.91  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.15/1.91  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.15/1.91  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.15/1.91  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.91  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.91  tff('#skF_1', type, '#skF_1': $i).
% 3.15/1.91  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.91  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.91  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.15/1.91  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.15/1.91  
% 3.15/1.92  tff(f_52, negated_conjecture, ~(![A, B]: (~(A = B) => (k5_xboole_0(k1_tarski(A), k1_tarski(B)) = k2_tarski(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t29_zfmisc_1)).
% 3.15/1.92  tff(f_37, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 3.15/1.92  tff(f_41, axiom, (![A, B]: (k3_xboole_0(k1_tarski(A), k2_tarski(A, B)) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t19_zfmisc_1)).
% 3.15/1.92  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.15/1.92  tff(f_46, axiom, (![A, B]: (~(A = B) => (k4_xboole_0(k2_tarski(A, B), k1_tarski(B)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t23_zfmisc_1)).
% 3.15/1.92  tff(f_31, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 3.15/1.92  tff(f_29, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.15/1.92  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.15/1.92  tff(c_22, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.15/1.92  tff(c_12, plain, (![B_12, A_11]: (k2_tarski(B_12, A_11)=k2_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.92  tff(c_16, plain, (![A_14, B_15]: (k3_xboole_0(k1_tarski(A_14), k2_tarski(A_14, B_15))=k1_tarski(A_14))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.15/1.92  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.92  tff(c_367, plain, (![A_43, B_44]: (k4_xboole_0(k2_tarski(A_43, B_44), k1_tarski(B_44))=k1_tarski(A_43) | B_44=A_43)), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.15/1.92  tff(c_379, plain, (![B_12, A_11]: (k4_xboole_0(k2_tarski(B_12, A_11), k1_tarski(B_12))=k1_tarski(A_11) | B_12=A_11)), inference(superposition, [status(thm), theory('equality')], [c_12, c_367])).
% 3.15/1.92  tff(c_6, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.15/1.92  tff(c_4, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k3_xboole_0(A_3, B_4))=k4_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.15/1.92  tff(c_304, plain, (![A_39, B_40]: (k5_xboole_0(k5_xboole_0(A_39, B_40), k3_xboole_0(A_39, B_40))=k2_xboole_0(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.15/1.92  tff(c_331, plain, (![A_3, B_4]: (k5_xboole_0(k4_xboole_0(A_3, B_4), k3_xboole_0(A_3, k3_xboole_0(A_3, B_4)))=k2_xboole_0(A_3, k3_xboole_0(A_3, B_4)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_304])).
% 3.15/1.92  tff(c_628, plain, (![A_57, B_58]: (k5_xboole_0(k4_xboole_0(A_57, B_58), k3_xboole_0(A_57, k3_xboole_0(A_57, B_58)))=A_57)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_331])).
% 3.15/1.92  tff(c_646, plain, (![A_11, B_12]: (k5_xboole_0(k1_tarski(A_11), k3_xboole_0(k2_tarski(B_12, A_11), k3_xboole_0(k2_tarski(B_12, A_11), k1_tarski(B_12))))=k2_tarski(B_12, A_11) | B_12=A_11)), inference(superposition, [status(thm), theory('equality')], [c_379, c_628])).
% 3.15/1.92  tff(c_870, plain, (![A_68, B_69]: (k5_xboole_0(k1_tarski(A_68), k1_tarski(B_69))=k2_tarski(B_69, A_68) | B_69=A_68)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_2, c_16, c_2, c_646])).
% 3.15/1.92  tff(c_20, plain, (k5_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))!=k2_tarski('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.15/1.92  tff(c_886, plain, (k2_tarski('#skF_2', '#skF_1')!=k2_tarski('#skF_1', '#skF_2') | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_870, c_20])).
% 3.15/1.92  tff(c_897, plain, ('#skF_2'='#skF_1'), inference(demodulation, [status(thm), theory('equality')], [c_12, c_886])).
% 3.15/1.92  tff(c_899, plain, $false, inference(negUnitSimplification, [status(thm)], [c_22, c_897])).
% 3.15/1.92  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.92  
% 3.15/1.92  Inference rules
% 3.15/1.92  ----------------------
% 3.15/1.92  #Ref     : 0
% 3.15/1.92  #Sup     : 217
% 3.15/1.92  #Fact    : 0
% 3.15/1.92  #Define  : 0
% 3.15/1.92  #Split   : 0
% 3.15/1.92  #Chain   : 0
% 3.15/1.92  #Close   : 0
% 3.15/1.92  
% 3.15/1.92  Ordering : KBO
% 3.15/1.92  
% 3.15/1.92  Simplification rules
% 3.15/1.92  ----------------------
% 3.15/1.92  #Subsume      : 9
% 3.15/1.92  #Demod        : 121
% 3.15/1.92  #Tautology    : 130
% 3.15/1.92  #SimpNegUnit  : 1
% 3.15/1.92  #BackRed      : 1
% 3.15/1.92  
% 3.15/1.92  #Partial instantiations: 0
% 3.15/1.92  #Strategies tried      : 1
% 3.15/1.92  
% 3.15/1.92  Timing (in seconds)
% 3.15/1.92  ----------------------
% 3.15/1.93  Preprocessing        : 0.45
% 3.15/1.93  Parsing              : 0.23
% 3.15/1.93  CNF conversion       : 0.03
% 3.15/1.93  Main loop            : 0.55
% 3.15/1.93  Inferencing          : 0.20
% 3.15/1.93  Reduction            : 0.21
% 3.15/1.93  Demodulation         : 0.17
% 3.15/1.93  BG Simplification    : 0.03
% 3.15/1.93  Subsumption          : 0.08
% 3.15/1.93  Abstraction          : 0.03
% 3.15/1.93  MUC search           : 0.00
% 3.15/1.93  Cooper               : 0.00
% 3.15/1.93  Total                : 1.03
% 3.15/1.93  Index Insertion      : 0.00
% 3.15/1.93  Index Deletion       : 0.00
% 3.15/1.93  Index Matching       : 0.00
% 3.15/1.93  BG Taut test         : 0.00
%------------------------------------------------------------------------------

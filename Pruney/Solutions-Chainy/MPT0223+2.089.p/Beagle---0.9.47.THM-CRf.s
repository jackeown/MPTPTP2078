%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n002.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:28 EST 2020

% Result     : Theorem 1.60s
% Output     : CNFRefutation 1.60s
% Verified   : 
% Statistics : Number of formulae       :   30 (  32 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    4
%              Number of atoms          :   29 (  33 expanded)
%              Number of equality atoms :   21 (  24 expanded)
%              Maximal formula depth    :    5 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_48,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,k3_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t22_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_38,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( A != B
     => r1_xboole_0(k1_tarski(A),k1_tarski(B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_zfmisc_1)).

tff(c_14,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_8,plain,(
    ! [A_5,B_6] : k2_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_27,plain,(
    ! [A_14,B_15] : k3_xboole_0(A_14,k2_xboole_0(A_14,B_15)) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_39,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_27])).

tff(c_54,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k3_xboole_0(A_17,B_18) != k1_xboole_0 ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_10,plain,(
    ! [B_8] : ~ r1_xboole_0(k1_tarski(B_8),k1_tarski(B_8)) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_58,plain,(
    ! [B_8] : k3_xboole_0(k1_tarski(B_8),k1_tarski(B_8)) != k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_54,c_10])).

tff(c_73,plain,(
    ! [B_8] : k1_tarski(B_8) != k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_39,c_58])).

tff(c_12,plain,(
    ! [A_9,B_10] :
      ( r1_xboole_0(k1_tarski(A_9),k1_tarski(B_10))
      | B_10 = A_9 ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_90,plain,(
    ! [A_23,B_24] :
      ( k3_xboole_0(A_23,B_24) = k1_xboole_0
      | ~ r1_xboole_0(A_23,B_24) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_101,plain,(
    ! [A_25,B_26] :
      ( k3_xboole_0(k1_tarski(A_25),k1_tarski(B_26)) = k1_xboole_0
      | B_26 = A_25 ) ),
    inference(resolution,[status(thm)],[c_12,c_90])).

tff(c_16,plain,(
    k3_xboole_0(k1_tarski('#skF_1'),k1_tarski('#skF_2')) = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_107,plain,
    ( k1_tarski('#skF_1') = k1_xboole_0
    | '#skF_2' = '#skF_1' ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_16])).

tff(c_127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_73,c_107])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n002.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 12:29:37 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.60/1.11  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.11  
% 1.60/1.11  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.12  %$ r1_xboole_0 > k3_xboole_0 > k2_xboole_0 > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 1.60/1.12  
% 1.60/1.12  %Foreground sorts:
% 1.60/1.12  
% 1.60/1.12  
% 1.60/1.12  %Background operators:
% 1.60/1.12  
% 1.60/1.12  
% 1.60/1.12  %Foreground operators:
% 1.60/1.12  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.60/1.12  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.60/1.12  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 1.60/1.12  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.60/1.12  tff('#skF_2', type, '#skF_2': $i).
% 1.60/1.12  tff('#skF_1', type, '#skF_1': $i).
% 1.60/1.12  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.60/1.12  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.60/1.12  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.60/1.12  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.60/1.12  
% 1.60/1.13  tff(f_48, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 1.60/1.13  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, k3_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t22_xboole_1)).
% 1.60/1.13  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 1.60/1.13  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d7_xboole_0)).
% 1.60/1.13  tff(f_38, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.60/1.13  tff(f_43, axiom, (![A, B]: (~(A = B) => r1_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_zfmisc_1)).
% 1.60/1.13  tff(c_14, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.60/1.13  tff(c_8, plain, (![A_5, B_6]: (k2_xboole_0(A_5, k3_xboole_0(A_5, B_6))=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 1.60/1.13  tff(c_27, plain, (![A_14, B_15]: (k3_xboole_0(A_14, k2_xboole_0(A_14, B_15))=A_14)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.60/1.13  tff(c_39, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(superposition, [status(thm), theory('equality')], [c_8, c_27])).
% 1.60/1.13  tff(c_54, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k3_xboole_0(A_17, B_18)!=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.60/1.13  tff(c_10, plain, (![B_8]: (~r1_xboole_0(k1_tarski(B_8), k1_tarski(B_8)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.60/1.13  tff(c_58, plain, (![B_8]: (k3_xboole_0(k1_tarski(B_8), k1_tarski(B_8))!=k1_xboole_0)), inference(resolution, [status(thm)], [c_54, c_10])).
% 1.60/1.13  tff(c_73, plain, (![B_8]: (k1_tarski(B_8)!=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_39, c_58])).
% 1.60/1.13  tff(c_12, plain, (![A_9, B_10]: (r1_xboole_0(k1_tarski(A_9), k1_tarski(B_10)) | B_10=A_9)), inference(cnfTransformation, [status(thm)], [f_43])).
% 1.60/1.13  tff(c_90, plain, (![A_23, B_24]: (k3_xboole_0(A_23, B_24)=k1_xboole_0 | ~r1_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.60/1.13  tff(c_101, plain, (![A_25, B_26]: (k3_xboole_0(k1_tarski(A_25), k1_tarski(B_26))=k1_xboole_0 | B_26=A_25)), inference(resolution, [status(thm)], [c_12, c_90])).
% 1.60/1.13  tff(c_16, plain, (k3_xboole_0(k1_tarski('#skF_1'), k1_tarski('#skF_2'))=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_48])).
% 1.60/1.13  tff(c_107, plain, (k1_tarski('#skF_1')=k1_xboole_0 | '#skF_2'='#skF_1'), inference(superposition, [status(thm), theory('equality')], [c_101, c_16])).
% 1.60/1.13  tff(c_127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_14, c_73, c_107])).
% 1.60/1.13  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.60/1.13  
% 1.60/1.13  Inference rules
% 1.60/1.13  ----------------------
% 1.60/1.13  #Ref     : 0
% 1.60/1.13  #Sup     : 26
% 1.60/1.13  #Fact    : 0
% 1.60/1.13  #Define  : 0
% 1.60/1.13  #Split   : 0
% 1.60/1.13  #Chain   : 0
% 1.60/1.13  #Close   : 0
% 1.60/1.13  
% 1.60/1.13  Ordering : KBO
% 1.60/1.13  
% 1.60/1.13  Simplification rules
% 1.60/1.13  ----------------------
% 1.60/1.13  #Subsume      : 0
% 1.60/1.13  #Demod        : 4
% 1.60/1.13  #Tautology    : 16
% 1.60/1.13  #SimpNegUnit  : 1
% 1.60/1.13  #BackRed      : 0
% 1.60/1.13  
% 1.60/1.13  #Partial instantiations: 0
% 1.60/1.13  #Strategies tried      : 1
% 1.60/1.13  
% 1.60/1.13  Timing (in seconds)
% 1.60/1.13  ----------------------
% 1.60/1.13  Preprocessing        : 0.26
% 1.60/1.13  Parsing              : 0.14
% 1.60/1.13  CNF conversion       : 0.02
% 1.60/1.13  Main loop            : 0.10
% 1.60/1.13  Inferencing          : 0.04
% 1.60/1.13  Reduction            : 0.03
% 1.60/1.13  Demodulation         : 0.02
% 1.60/1.13  BG Simplification    : 0.01
% 1.60/1.13  Subsumption          : 0.01
% 1.60/1.13  Abstraction          : 0.00
% 1.60/1.13  MUC search           : 0.00
% 1.60/1.13  Cooper               : 0.00
% 1.60/1.13  Total                : 0.38
% 1.60/1.13  Index Insertion      : 0.00
% 1.60/1.13  Index Deletion       : 0.00
% 1.60/1.13  Index Matching       : 0.00
% 1.60/1.13  BG Taut test         : 0.00
%------------------------------------------------------------------------------

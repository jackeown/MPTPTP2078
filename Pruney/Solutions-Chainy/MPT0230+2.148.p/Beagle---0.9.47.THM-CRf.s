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
% DateTime   : Thu Dec  3 09:49:14 EST 2020

% Result     : Theorem 1.64s
% Output     : CNFRefutation 1.64s
% Verified   : 
% Statistics : Number of formulae       :   29 (  31 expanded)
%              Number of leaves         :   16 (  18 expanded)
%              Depth                    :    7
%              Number of atoms          :   31 (  37 expanded)
%              Number of equality atoms :   16 (  20 expanded)
%              Maximal formula depth    :    9 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_xboole_0(k1_tarski(A),k1_tarski(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t41_enumset1)).

tff(f_36,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_40,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),k1_tarski(B))
     => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(c_12,plain,(
    '#skF_3' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_14,plain,(
    '#skF_2' != '#skF_1' ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_16,plain,(
    r1_tarski(k1_tarski('#skF_1'),k2_tarski('#skF_2','#skF_3')) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_4,B_5] : k2_xboole_0(k1_tarski(A_4),k1_tarski(B_5)) = k2_tarski(A_4,B_5) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_8,plain,(
    ! [A_6,B_7] :
      ( k4_xboole_0(k1_tarski(A_6),k1_tarski(B_7)) = k1_tarski(A_6)
      | B_7 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_36])).

tff(c_44,plain,(
    ! [A_17,B_18,C_19] :
      ( r1_tarski(k4_xboole_0(A_17,B_18),C_19)
      | ~ r1_tarski(A_17,k2_xboole_0(B_18,C_19)) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_48,plain,(
    ! [A_20,C_21,B_22] :
      ( r1_tarski(k1_tarski(A_20),C_21)
      | ~ r1_tarski(k1_tarski(A_20),k2_xboole_0(k1_tarski(B_22),C_21))
      | B_22 = A_20 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_44])).

tff(c_52,plain,(
    ! [A_23,B_24,A_25] :
      ( r1_tarski(k1_tarski(A_23),k1_tarski(B_24))
      | ~ r1_tarski(k1_tarski(A_23),k2_tarski(A_25,B_24))
      | A_25 = A_23 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_48])).

tff(c_55,plain,
    ( r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3'))
    | '#skF_2' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_16,c_52])).

tff(c_58,plain,(
    r1_tarski(k1_tarski('#skF_1'),k1_tarski('#skF_3')) ),
    inference(negUnitSimplification,[status(thm)],[c_14,c_55])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(k1_tarski(A_8),k1_tarski(B_9)) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_61,plain,(
    '#skF_3' = '#skF_1' ),
    inference(resolution,[status(thm)],[c_58,c_10])).

tff(c_65,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_12,c_61])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:04:31 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.64/1.07  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.08  
% 1.64/1.08  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.08  %$ r1_tarski > k4_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1
% 1.64/1.08  
% 1.64/1.08  %Foreground sorts:
% 1.64/1.08  
% 1.64/1.08  
% 1.64/1.08  %Background operators:
% 1.64/1.08  
% 1.64/1.08  
% 1.64/1.08  %Foreground operators:
% 1.64/1.08  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.64/1.08  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.64/1.08  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.64/1.08  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 1.64/1.08  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.64/1.08  tff('#skF_2', type, '#skF_2': $i).
% 1.64/1.08  tff('#skF_3', type, '#skF_3': $i).
% 1.64/1.08  tff('#skF_1', type, '#skF_1': $i).
% 1.64/1.08  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.64/1.08  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.64/1.08  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 1.64/1.08  
% 1.64/1.09  tff(f_50, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 1.64/1.09  tff(f_31, axiom, (![A, B]: (k2_tarski(A, B) = k2_xboole_0(k1_tarski(A), k1_tarski(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t41_enumset1)).
% 1.64/1.09  tff(f_36, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.64/1.09  tff(f_29, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_xboole_1)).
% 1.64/1.09  tff(f_40, axiom, (![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 1.64/1.09  tff(c_12, plain, ('#skF_3'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.64/1.09  tff(c_14, plain, ('#skF_2'!='#skF_1'), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.64/1.09  tff(c_16, plain, (r1_tarski(k1_tarski('#skF_1'), k2_tarski('#skF_2', '#skF_3'))), inference(cnfTransformation, [status(thm)], [f_50])).
% 1.64/1.09  tff(c_4, plain, (![A_4, B_5]: (k2_xboole_0(k1_tarski(A_4), k1_tarski(B_5))=k2_tarski(A_4, B_5))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.64/1.09  tff(c_8, plain, (![A_6, B_7]: (k4_xboole_0(k1_tarski(A_6), k1_tarski(B_7))=k1_tarski(A_6) | B_7=A_6)), inference(cnfTransformation, [status(thm)], [f_36])).
% 1.64/1.09  tff(c_44, plain, (![A_17, B_18, C_19]: (r1_tarski(k4_xboole_0(A_17, B_18), C_19) | ~r1_tarski(A_17, k2_xboole_0(B_18, C_19)))), inference(cnfTransformation, [status(thm)], [f_29])).
% 1.64/1.09  tff(c_48, plain, (![A_20, C_21, B_22]: (r1_tarski(k1_tarski(A_20), C_21) | ~r1_tarski(k1_tarski(A_20), k2_xboole_0(k1_tarski(B_22), C_21)) | B_22=A_20)), inference(superposition, [status(thm), theory('equality')], [c_8, c_44])).
% 1.64/1.09  tff(c_52, plain, (![A_23, B_24, A_25]: (r1_tarski(k1_tarski(A_23), k1_tarski(B_24)) | ~r1_tarski(k1_tarski(A_23), k2_tarski(A_25, B_24)) | A_25=A_23)), inference(superposition, [status(thm), theory('equality')], [c_4, c_48])).
% 1.64/1.09  tff(c_55, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3')) | '#skF_2'='#skF_1'), inference(resolution, [status(thm)], [c_16, c_52])).
% 1.64/1.09  tff(c_58, plain, (r1_tarski(k1_tarski('#skF_1'), k1_tarski('#skF_3'))), inference(negUnitSimplification, [status(thm)], [c_14, c_55])).
% 1.64/1.09  tff(c_10, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(k1_tarski(A_8), k1_tarski(B_9)))), inference(cnfTransformation, [status(thm)], [f_40])).
% 1.64/1.09  tff(c_61, plain, ('#skF_3'='#skF_1'), inference(resolution, [status(thm)], [c_58, c_10])).
% 1.64/1.09  tff(c_65, plain, $false, inference(negUnitSimplification, [status(thm)], [c_12, c_61])).
% 1.64/1.09  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.64/1.09  
% 1.64/1.09  Inference rules
% 1.64/1.09  ----------------------
% 1.64/1.09  #Ref     : 0
% 1.64/1.09  #Sup     : 9
% 1.64/1.09  #Fact    : 0
% 1.64/1.09  #Define  : 0
% 1.64/1.09  #Split   : 0
% 1.64/1.09  #Chain   : 0
% 1.64/1.09  #Close   : 0
% 1.64/1.09  
% 1.64/1.09  Ordering : KBO
% 1.64/1.09  
% 1.64/1.09  Simplification rules
% 1.64/1.09  ----------------------
% 1.64/1.09  #Subsume      : 0
% 1.64/1.09  #Demod        : 0
% 1.64/1.09  #Tautology    : 5
% 1.64/1.09  #SimpNegUnit  : 2
% 1.64/1.09  #BackRed      : 0
% 1.64/1.09  
% 1.64/1.09  #Partial instantiations: 0
% 1.64/1.09  #Strategies tried      : 1
% 1.64/1.09  
% 1.64/1.09  Timing (in seconds)
% 1.64/1.09  ----------------------
% 1.64/1.09  Preprocessing        : 0.26
% 1.64/1.09  Parsing              : 0.14
% 1.64/1.09  CNF conversion       : 0.02
% 1.64/1.09  Main loop            : 0.08
% 1.64/1.09  Inferencing          : 0.04
% 1.64/1.09  Reduction            : 0.02
% 1.64/1.09  Demodulation         : 0.01
% 1.64/1.09  BG Simplification    : 0.01
% 1.64/1.09  Subsumption          : 0.01
% 1.64/1.09  Abstraction          : 0.00
% 1.64/1.09  MUC search           : 0.00
% 1.64/1.09  Cooper               : 0.00
% 1.64/1.09  Total                : 0.37
% 1.64/1.09  Index Insertion      : 0.00
% 1.64/1.09  Index Deletion       : 0.00
% 1.64/1.09  Index Matching       : 0.00
% 1.64/1.09  BG Taut test         : 0.00
%------------------------------------------------------------------------------

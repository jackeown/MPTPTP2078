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
% DateTime   : Thu Dec  3 09:48:36 EST 2020

% Result     : Theorem 1.85s
% Output     : CNFRefutation 1.85s
% Verified   : 
% Statistics : Number of formulae       :   49 (  70 expanded)
%              Number of leaves         :   23 (  35 expanded)
%              Depth                    :    5
%              Number of atoms          :   47 (  86 expanded)
%              Number of equality atoms :   30 (  65 expanded)
%              Maximal formula depth    :    6 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1

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

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i ) > $i )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_54,axiom,(
    ! [A,B] :
      ~ ( r1_xboole_0(k1_tarski(A),k1_tarski(B))
        & A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_zfmisc_1)).

tff(f_60,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_38,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(c_247,plain,(
    ! [A_66,B_67] :
      ( r1_xboole_0(A_66,B_67)
      | k4_xboole_0(A_66,B_67) != A_66 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_28,plain,(
    ! [B_19] : ~ r1_xboole_0(k1_tarski(B_19),k1_tarski(B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_251,plain,(
    ! [B_19] : k4_xboole_0(k1_tarski(B_19),k1_tarski(B_19)) != k1_tarski(B_19) ),
    inference(resolution,[status(thm)],[c_247,c_28])).

tff(c_71,plain,(
    ! [A_29,B_30] :
      ( r1_xboole_0(A_29,B_30)
      | k4_xboole_0(A_29,B_30) != A_29 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_75,plain,(
    ! [B_19] : k4_xboole_0(k1_tarski(B_19),k1_tarski(B_19)) != k1_tarski(B_19) ),
    inference(resolution,[status(thm)],[c_71,c_28])).

tff(c_32,plain,
    ( '#skF_3' != '#skF_4'
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_37,plain,(
    '#skF_3' != '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_26,plain,(
    ! [A_16,B_17] :
      ( r1_xboole_0(k1_tarski(A_16),B_17)
      | r2_hidden(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_77,plain,(
    ! [A_31,B_32] :
      ( k4_xboole_0(A_31,B_32) = A_31
      | ~ r1_xboole_0(A_31,B_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_105,plain,(
    ! [A_39,B_40] :
      ( k4_xboole_0(k1_tarski(A_39),B_40) = k1_tarski(A_39)
      | r2_hidden(A_39,B_40) ) ),
    inference(resolution,[status(thm)],[c_26,c_77])).

tff(c_30,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | '#skF_5' = '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_76,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_122,plain,(
    r2_hidden('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_105,c_76])).

tff(c_8,plain,(
    ! [C_9,A_5] :
      ( C_9 = A_5
      | ~ r2_hidden(C_9,k1_tarski(A_5)) ) ),
    inference(cnfTransformation,[status(thm)],[f_38])).

tff(c_126,plain,(
    '#skF_3' = '#skF_4' ),
    inference(resolution,[status(thm)],[c_122,c_8])).

tff(c_130,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_37,c_126])).

tff(c_131,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_132,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_34,plain,
    ( k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) != k1_tarski('#skF_3')
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_202,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_131,c_131,c_132,c_34])).

tff(c_203,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_75,c_202])).

tff(c_204,plain,(
    '#skF_5' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_205,plain,(
    '#skF_3' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_36,plain,
    ( '#skF_3' != '#skF_4'
    | k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_282,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_6')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_204,c_204,c_205,c_36])).

tff(c_283,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_251,c_282])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n019.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 19:36:37 EST 2020
% 0.12/0.33  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 1.85/1.19  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.20  
% 1.85/1.20  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.20  %$ r2_hidden > r1_xboole_0 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_2 > #skF_1
% 1.85/1.20  
% 1.85/1.20  %Foreground sorts:
% 1.85/1.20  
% 1.85/1.20  
% 1.85/1.20  %Background operators:
% 1.85/1.20  
% 1.85/1.20  
% 1.85/1.20  %Foreground operators:
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 1.85/1.20  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 1.85/1.20  tff(k1_tarski, type, k1_tarski: $i > $i).
% 1.85/1.20  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 1.85/1.20  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 1.85/1.20  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 1.85/1.20  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 1.85/1.20  tff('#skF_5', type, '#skF_5': $i).
% 1.85/1.20  tff('#skF_6', type, '#skF_6': $i).
% 1.85/1.20  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 1.85/1.20  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 1.85/1.20  tff('#skF_3', type, '#skF_3': $i).
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 1.85/1.20  tff('#skF_4', type, '#skF_4': $i).
% 1.85/1.20  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 1.85/1.20  tff('#skF_2', type, '#skF_2': ($i * $i) > $i).
% 1.85/1.20  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 1.85/1.20  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 1.85/1.20  
% 1.85/1.21  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 1.85/1.21  tff(f_54, axiom, (![A, B]: ~(r1_xboole_0(k1_tarski(A), k1_tarski(B)) & (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_zfmisc_1)).
% 1.85/1.21  tff(f_60, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 1.85/1.21  tff(f_49, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 1.85/1.21  tff(f_38, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 1.85/1.21  tff(c_247, plain, (![A_66, B_67]: (r1_xboole_0(A_66, B_67) | k4_xboole_0(A_66, B_67)!=A_66)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.21  tff(c_28, plain, (![B_19]: (~r1_xboole_0(k1_tarski(B_19), k1_tarski(B_19)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 1.85/1.21  tff(c_251, plain, (![B_19]: (k4_xboole_0(k1_tarski(B_19), k1_tarski(B_19))!=k1_tarski(B_19))), inference(resolution, [status(thm)], [c_247, c_28])).
% 1.85/1.21  tff(c_71, plain, (![A_29, B_30]: (r1_xboole_0(A_29, B_30) | k4_xboole_0(A_29, B_30)!=A_29)), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.21  tff(c_75, plain, (![B_19]: (k4_xboole_0(k1_tarski(B_19), k1_tarski(B_19))!=k1_tarski(B_19))), inference(resolution, [status(thm)], [c_71, c_28])).
% 1.85/1.21  tff(c_32, plain, ('#skF_3'!='#skF_4' | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.21  tff(c_37, plain, ('#skF_3'!='#skF_4'), inference(splitLeft, [status(thm)], [c_32])).
% 1.85/1.21  tff(c_26, plain, (![A_16, B_17]: (r1_xboole_0(k1_tarski(A_16), B_17) | r2_hidden(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_49])).
% 1.85/1.21  tff(c_77, plain, (![A_31, B_32]: (k4_xboole_0(A_31, B_32)=A_31 | ~r1_xboole_0(A_31, B_32))), inference(cnfTransformation, [status(thm)], [f_31])).
% 1.85/1.21  tff(c_105, plain, (![A_39, B_40]: (k4_xboole_0(k1_tarski(A_39), B_40)=k1_tarski(A_39) | r2_hidden(A_39, B_40))), inference(resolution, [status(thm)], [c_26, c_77])).
% 1.85/1.21  tff(c_30, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | '#skF_5'='#skF_6'), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.21  tff(c_76, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3')), inference(splitLeft, [status(thm)], [c_30])).
% 1.85/1.21  tff(c_122, plain, (r2_hidden('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_105, c_76])).
% 1.85/1.21  tff(c_8, plain, (![C_9, A_5]: (C_9=A_5 | ~r2_hidden(C_9, k1_tarski(A_5)))), inference(cnfTransformation, [status(thm)], [f_38])).
% 1.85/1.21  tff(c_126, plain, ('#skF_3'='#skF_4'), inference(resolution, [status(thm)], [c_122, c_8])).
% 1.85/1.21  tff(c_130, plain, $false, inference(negUnitSimplification, [status(thm)], [c_37, c_126])).
% 1.85/1.21  tff(c_131, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_30])).
% 1.85/1.21  tff(c_132, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(splitRight, [status(thm)], [c_30])).
% 1.85/1.21  tff(c_34, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))!=k1_tarski('#skF_3') | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.21  tff(c_202, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_131, c_131, c_132, c_34])).
% 1.85/1.21  tff(c_203, plain, $false, inference(negUnitSimplification, [status(thm)], [c_75, c_202])).
% 1.85/1.21  tff(c_204, plain, ('#skF_5'='#skF_6'), inference(splitRight, [status(thm)], [c_32])).
% 1.85/1.21  tff(c_205, plain, ('#skF_3'='#skF_4'), inference(splitRight, [status(thm)], [c_32])).
% 1.85/1.21  tff(c_36, plain, ('#skF_3'!='#skF_4' | k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_60])).
% 1.85/1.21  tff(c_282, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_6'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_204, c_204, c_205, c_36])).
% 1.85/1.21  tff(c_283, plain, $false, inference(negUnitSimplification, [status(thm)], [c_251, c_282])).
% 1.85/1.21  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 1.85/1.21  
% 1.85/1.21  Inference rules
% 1.85/1.21  ----------------------
% 1.85/1.21  #Ref     : 0
% 1.85/1.21  #Sup     : 51
% 1.85/1.21  #Fact    : 0
% 1.85/1.21  #Define  : 0
% 1.85/1.21  #Split   : 2
% 1.85/1.21  #Chain   : 0
% 1.85/1.21  #Close   : 0
% 1.85/1.21  
% 1.85/1.21  Ordering : KBO
% 1.85/1.21  
% 1.85/1.21  Simplification rules
% 1.85/1.21  ----------------------
% 1.85/1.21  #Subsume      : 2
% 1.85/1.21  #Demod        : 15
% 1.85/1.21  #Tautology    : 44
% 1.85/1.21  #SimpNegUnit  : 3
% 1.85/1.21  #BackRed      : 0
% 1.85/1.21  
% 1.85/1.21  #Partial instantiations: 0
% 1.85/1.21  #Strategies tried      : 1
% 1.85/1.21  
% 1.85/1.21  Timing (in seconds)
% 1.85/1.21  ----------------------
% 1.85/1.21  Preprocessing        : 0.29
% 1.85/1.21  Parsing              : 0.15
% 1.85/1.21  CNF conversion       : 0.02
% 1.85/1.21  Main loop            : 0.17
% 1.85/1.21  Inferencing          : 0.07
% 1.85/1.21  Reduction            : 0.05
% 1.85/1.21  Demodulation         : 0.03
% 1.85/1.21  BG Simplification    : 0.01
% 1.85/1.21  Subsumption          : 0.03
% 1.85/1.21  Abstraction          : 0.01
% 1.85/1.21  MUC search           : 0.00
% 1.85/1.22  Cooper               : 0.00
% 1.85/1.22  Total                : 0.49
% 1.85/1.22  Index Insertion      : 0.00
% 1.85/1.22  Index Deletion       : 0.00
% 1.85/1.22  Index Matching       : 0.00
% 1.85/1.22  BG Taut test         : 0.00
%------------------------------------------------------------------------------

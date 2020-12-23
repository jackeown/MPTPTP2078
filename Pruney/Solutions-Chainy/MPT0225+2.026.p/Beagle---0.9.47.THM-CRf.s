%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:34 EST 2020

% Result     : Theorem 2.44s
% Output     : CNFRefutation 2.58s
% Verified   : 
% Statistics : Number of formulae       :   64 ( 110 expanded)
%              Number of leaves         :   26 (  50 expanded)
%              Depth                    :    8
%              Number of atoms          :   73 ( 185 expanded)
%              Number of equality atoms :   34 (  91 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_71,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_tarski)).

tff(f_85,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
      <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] :
              ~ ( r2_hidden(C,A)
                & r2_hidden(C,B) ) )
      & ~ ( ? [C] :
              ( r2_hidden(C,A)
              & r2_hidden(C,B) )
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_xboole_0)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(c_40,plain,(
    ! [C_21] : r2_hidden(C_21,k1_tarski(C_21)) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_60,plain,
    ( '#skF_7' != '#skF_6'
    | '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_65,plain,(
    '#skF_7' != '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_58,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_tarski('#skF_6')
    | '#skF_9' = '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_103,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_tarski('#skF_6') ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_136,plain,(
    ! [A_59,B_60] :
      ( r2_hidden('#skF_1'(A_59,B_60),B_60)
      | r1_xboole_0(A_59,B_60) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_38,plain,(
    ! [C_21,A_17] :
      ( C_21 = A_17
      | ~ r2_hidden(C_21,k1_tarski(A_17)) ) ),
    inference(cnfTransformation,[status(thm)],[f_71])).

tff(c_163,plain,(
    ! [A_69,A_70] :
      ( '#skF_1'(A_69,k1_tarski(A_70)) = A_70
      | r1_xboole_0(A_69,k1_tarski(A_70)) ) ),
    inference(resolution,[status(thm)],[c_136,c_38])).

tff(c_10,plain,(
    ! [A_8,B_9] :
      ( k4_xboole_0(A_8,B_9) = A_8
      | ~ r1_xboole_0(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_223,plain,(
    ! [A_94,A_95] :
      ( k4_xboole_0(A_94,k1_tarski(A_95)) = A_94
      | '#skF_1'(A_94,k1_tarski(A_95)) = A_95 ) ),
    inference(resolution,[status(thm)],[c_163,c_10])).

tff(c_238,plain,(
    '#skF_1'(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_223,c_103])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_246,plain,
    ( r2_hidden('#skF_7',k1_tarski('#skF_6'))
    | r1_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_6])).

tff(c_276,plain,(
    r1_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) ),
    inference(splitLeft,[status(thm)],[c_246])).

tff(c_281,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(resolution,[status(thm)],[c_276,c_10])).

tff(c_286,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_103,c_281])).

tff(c_287,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_246])).

tff(c_293,plain,(
    '#skF_7' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_287,c_38])).

tff(c_298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_65,c_293])).

tff(c_299,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_300,plain,(
    k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) = k1_tarski('#skF_6') ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_62,plain,
    ( k4_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_7')) != k1_tarski('#skF_6')
    | k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_9')) = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_342,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_299,c_300,c_62])).

tff(c_12,plain,(
    ! [A_8,B_9] :
      ( r1_xboole_0(A_8,B_9)
      | k4_xboole_0(A_8,B_9) != A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_353,plain,(
    ! [A_114,B_115,C_116] :
      ( ~ r1_xboole_0(A_114,B_115)
      | ~ r2_hidden(C_116,B_115)
      | ~ r2_hidden(C_116,A_114) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_383,plain,(
    ! [C_126,B_127,A_128] :
      ( ~ r2_hidden(C_126,B_127)
      | ~ r2_hidden(C_126,A_128)
      | k4_xboole_0(A_128,B_127) != A_128 ) ),
    inference(resolution,[status(thm)],[c_12,c_353])).

tff(c_408,plain,(
    ! [C_129,A_130] :
      ( ~ r2_hidden(C_129,A_130)
      | k4_xboole_0(A_130,k1_tarski(C_129)) != A_130 ) ),
    inference(resolution,[status(thm)],[c_40,c_383])).

tff(c_411,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_342,c_408])).

tff(c_418,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_411])).

tff(c_419,plain,(
    '#skF_9' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_420,plain,(
    '#skF_7' = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_64,plain,
    ( '#skF_7' != '#skF_6'
    | k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_9')) = k1_tarski('#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_469,plain,(
    k4_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_8')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_419,c_420,c_64])).

tff(c_511,plain,(
    ! [A_160,B_161,C_162] :
      ( ~ r1_xboole_0(A_160,B_161)
      | ~ r2_hidden(C_162,B_161)
      | ~ r2_hidden(C_162,A_160) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_541,plain,(
    ! [C_170,B_171,A_172] :
      ( ~ r2_hidden(C_170,B_171)
      | ~ r2_hidden(C_170,A_172)
      | k4_xboole_0(A_172,B_171) != A_172 ) ),
    inference(resolution,[status(thm)],[c_12,c_511])).

tff(c_566,plain,(
    ! [C_173,A_174] :
      ( ~ r2_hidden(C_173,A_174)
      | k4_xboole_0(A_174,k1_tarski(C_173)) != A_174 ) ),
    inference(resolution,[status(thm)],[c_40,c_541])).

tff(c_569,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_469,c_566])).

tff(c_573,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_569])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n009.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 16:15:41 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.44/1.37  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.37  
% 2.58/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.38  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 2.58/1.38  
% 2.58/1.38  %Foreground sorts:
% 2.58/1.38  
% 2.58/1.38  
% 2.58/1.38  %Background operators:
% 2.58/1.38  
% 2.58/1.38  
% 2.58/1.38  %Foreground operators:
% 2.58/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.58/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.58/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.58/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.58/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.58/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.58/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.58/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.58/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.58/1.38  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 2.58/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.58/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.58/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.58/1.38  tff('#skF_9', type, '#skF_9': $i).
% 2.58/1.38  tff('#skF_8', type, '#skF_8': $i).
% 2.58/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.58/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.58/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.58/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.58/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.58/1.38  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 2.58/1.38  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.58/1.38  
% 2.58/1.39  tff(f_71, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_tarski)).
% 2.58/1.39  tff(f_85, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.58/1.39  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~(r2_hidden(C, A) & r2_hidden(C, B)))) & ~((?[C]: (r2_hidden(C, A) & r2_hidden(C, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_xboole_0)).
% 2.58/1.39  tff(f_49, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.58/1.39  tff(c_40, plain, (![C_21]: (r2_hidden(C_21, k1_tarski(C_21)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.58/1.39  tff(c_60, plain, ('#skF_7'!='#skF_6' | '#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.58/1.39  tff(c_65, plain, ('#skF_7'!='#skF_6'), inference(splitLeft, [status(thm)], [c_60])).
% 2.58/1.39  tff(c_58, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_tarski('#skF_6') | '#skF_9'='#skF_8'), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.58/1.39  tff(c_103, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_tarski('#skF_6')), inference(splitLeft, [status(thm)], [c_58])).
% 2.58/1.39  tff(c_136, plain, (![A_59, B_60]: (r2_hidden('#skF_1'(A_59, B_60), B_60) | r1_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.58/1.39  tff(c_38, plain, (![C_21, A_17]: (C_21=A_17 | ~r2_hidden(C_21, k1_tarski(A_17)))), inference(cnfTransformation, [status(thm)], [f_71])).
% 2.58/1.39  tff(c_163, plain, (![A_69, A_70]: ('#skF_1'(A_69, k1_tarski(A_70))=A_70 | r1_xboole_0(A_69, k1_tarski(A_70)))), inference(resolution, [status(thm)], [c_136, c_38])).
% 2.58/1.39  tff(c_10, plain, (![A_8, B_9]: (k4_xboole_0(A_8, B_9)=A_8 | ~r1_xboole_0(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.58/1.39  tff(c_223, plain, (![A_94, A_95]: (k4_xboole_0(A_94, k1_tarski(A_95))=A_94 | '#skF_1'(A_94, k1_tarski(A_95))=A_95)), inference(resolution, [status(thm)], [c_163, c_10])).
% 2.58/1.39  tff(c_238, plain, ('#skF_1'(k1_tarski('#skF_6'), k1_tarski('#skF_7'))='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_223, c_103])).
% 2.58/1.39  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.58/1.39  tff(c_246, plain, (r2_hidden('#skF_7', k1_tarski('#skF_6')) | r1_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_238, c_6])).
% 2.58/1.39  tff(c_276, plain, (r1_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))), inference(splitLeft, [status(thm)], [c_246])).
% 2.58/1.39  tff(c_281, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(resolution, [status(thm)], [c_276, c_10])).
% 2.58/1.39  tff(c_286, plain, $false, inference(negUnitSimplification, [status(thm)], [c_103, c_281])).
% 2.58/1.39  tff(c_287, plain, (r2_hidden('#skF_7', k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_246])).
% 2.58/1.39  tff(c_293, plain, ('#skF_7'='#skF_6'), inference(resolution, [status(thm)], [c_287, c_38])).
% 2.58/1.39  tff(c_298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_65, c_293])).
% 2.58/1.39  tff(c_299, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_58])).
% 2.58/1.39  tff(c_300, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))=k1_tarski('#skF_6')), inference(splitRight, [status(thm)], [c_58])).
% 2.58/1.39  tff(c_62, plain, (k4_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_7'))!=k1_tarski('#skF_6') | k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_9'))=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.58/1.39  tff(c_342, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_299, c_300, c_62])).
% 2.58/1.39  tff(c_12, plain, (![A_8, B_9]: (r1_xboole_0(A_8, B_9) | k4_xboole_0(A_8, B_9)!=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.58/1.39  tff(c_353, plain, (![A_114, B_115, C_116]: (~r1_xboole_0(A_114, B_115) | ~r2_hidden(C_116, B_115) | ~r2_hidden(C_116, A_114))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.58/1.39  tff(c_383, plain, (![C_126, B_127, A_128]: (~r2_hidden(C_126, B_127) | ~r2_hidden(C_126, A_128) | k4_xboole_0(A_128, B_127)!=A_128)), inference(resolution, [status(thm)], [c_12, c_353])).
% 2.58/1.39  tff(c_408, plain, (![C_129, A_130]: (~r2_hidden(C_129, A_130) | k4_xboole_0(A_130, k1_tarski(C_129))!=A_130)), inference(resolution, [status(thm)], [c_40, c_383])).
% 2.58/1.39  tff(c_411, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_342, c_408])).
% 2.58/1.39  tff(c_418, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_411])).
% 2.58/1.39  tff(c_419, plain, ('#skF_9'='#skF_8'), inference(splitRight, [status(thm)], [c_60])).
% 2.58/1.39  tff(c_420, plain, ('#skF_7'='#skF_6'), inference(splitRight, [status(thm)], [c_60])).
% 2.58/1.39  tff(c_64, plain, ('#skF_7'!='#skF_6' | k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_9'))=k1_tarski('#skF_8')), inference(cnfTransformation, [status(thm)], [f_85])).
% 2.58/1.39  tff(c_469, plain, (k4_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_8'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_419, c_420, c_64])).
% 2.58/1.39  tff(c_511, plain, (![A_160, B_161, C_162]: (~r1_xboole_0(A_160, B_161) | ~r2_hidden(C_162, B_161) | ~r2_hidden(C_162, A_160))), inference(cnfTransformation, [status(thm)], [f_43])).
% 2.58/1.39  tff(c_541, plain, (![C_170, B_171, A_172]: (~r2_hidden(C_170, B_171) | ~r2_hidden(C_170, A_172) | k4_xboole_0(A_172, B_171)!=A_172)), inference(resolution, [status(thm)], [c_12, c_511])).
% 2.58/1.39  tff(c_566, plain, (![C_173, A_174]: (~r2_hidden(C_173, A_174) | k4_xboole_0(A_174, k1_tarski(C_173))!=A_174)), inference(resolution, [status(thm)], [c_40, c_541])).
% 2.58/1.39  tff(c_569, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_469, c_566])).
% 2.58/1.39  tff(c_573, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_40, c_569])).
% 2.58/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.58/1.39  
% 2.58/1.39  Inference rules
% 2.58/1.39  ----------------------
% 2.58/1.39  #Ref     : 0
% 2.58/1.39  #Sup     : 121
% 2.58/1.39  #Fact    : 0
% 2.58/1.39  #Define  : 0
% 2.58/1.39  #Split   : 3
% 2.58/1.39  #Chain   : 0
% 2.58/1.39  #Close   : 0
% 2.58/1.39  
% 2.58/1.39  Ordering : KBO
% 2.58/1.39  
% 2.58/1.39  Simplification rules
% 2.58/1.39  ----------------------
% 2.58/1.39  #Subsume      : 7
% 2.58/1.39  #Demod        : 21
% 2.58/1.39  #Tautology    : 61
% 2.58/1.39  #SimpNegUnit  : 2
% 2.58/1.39  #BackRed      : 0
% 2.58/1.39  
% 2.58/1.39  #Partial instantiations: 0
% 2.58/1.39  #Strategies tried      : 1
% 2.58/1.39  
% 2.58/1.39  Timing (in seconds)
% 2.58/1.39  ----------------------
% 2.58/1.39  Preprocessing        : 0.33
% 2.58/1.39  Parsing              : 0.17
% 2.58/1.39  CNF conversion       : 0.03
% 2.58/1.39  Main loop            : 0.27
% 2.58/1.39  Inferencing          : 0.10
% 2.58/1.39  Reduction            : 0.08
% 2.58/1.39  Demodulation         : 0.06
% 2.58/1.39  BG Simplification    : 0.02
% 2.58/1.39  Subsumption          : 0.05
% 2.58/1.39  Abstraction          : 0.02
% 2.58/1.39  MUC search           : 0.00
% 2.58/1.39  Cooper               : 0.00
% 2.58/1.39  Total                : 0.63
% 2.58/1.39  Index Insertion      : 0.00
% 2.58/1.39  Index Deletion       : 0.00
% 2.58/1.39  Index Matching       : 0.00
% 2.58/1.39  BG Taut test         : 0.00
%------------------------------------------------------------------------------

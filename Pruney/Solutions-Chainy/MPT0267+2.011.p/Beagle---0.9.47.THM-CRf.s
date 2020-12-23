%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:33 EST 2020

% Result     : Theorem 2.28s
% Output     : CNFRefutation 2.28s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 168 expanded)
%              Number of leaves         :   19 (  59 expanded)
%              Depth                    :   11
%              Number of atoms          :   93 ( 327 expanded)
%              Number of equality atoms :   23 ( 115 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k4_xboole_0 > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_42,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_50,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
      <=> ( r2_hidden(A,B)
          & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_22,plain,(
    ! [C_11] : r2_hidden(C_11,k1_tarski(C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_34,plain,
    ( '#skF_7' != '#skF_5'
    | '#skF_10' = '#skF_8'
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_50,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_40,plain,
    ( '#skF_7' != '#skF_5'
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_52,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_42,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_54,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitLeft,[status(thm)],[c_42])).

tff(c_6,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,A_1)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_60,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_54,c_6])).

tff(c_65,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_60])).

tff(c_66,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_2,plain,(
    ! [D_6,A_1,B_2] :
      ( r2_hidden(D_6,k4_xboole_0(A_1,B_2))
      | r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,A_1) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_67,plain,(
    ~ r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_42])).

tff(c_38,plain,
    ( ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_238,plain,(
    ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_67,c_38])).

tff(c_241,plain,
    ( r2_hidden('#skF_5',k1_tarski('#skF_7'))
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_238])).

tff(c_249,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_241])).

tff(c_20,plain,(
    ! [C_11,A_7] :
      ( C_11 = A_7
      | ~ r2_hidden(C_11,k1_tarski(A_7)) ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_252,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_249,c_20])).

tff(c_298,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_52,c_252])).

tff(c_299,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_10'))) ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_307,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_299,c_6])).

tff(c_311,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_307])).

tff(c_312,plain,
    ( '#skF_7' != '#skF_5'
    | '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_314,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_312])).

tff(c_313,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | '#skF_10' = '#skF_8'
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_316,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_36])).

tff(c_317,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_316])).

tff(c_325,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_42])).

tff(c_326,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_325])).

tff(c_4,plain,(
    ! [D_6,B_2,A_1] :
      ( ~ r2_hidden(D_6,B_2)
      | ~ r2_hidden(D_6,k4_xboole_0(A_1,B_2)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_332,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_326,c_4])).

tff(c_338,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_332])).

tff(c_339,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_340,plain,(
    ~ r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_325])).

tff(c_516,plain,
    ( ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_317,c_38])).

tff(c_517,plain,(
    ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_340,c_516])).

tff(c_520,plain,
    ( r2_hidden('#skF_5',k1_tarski('#skF_7'))
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_2,c_517])).

tff(c_528,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_339,c_520])).

tff(c_531,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_528,c_20])).

tff(c_577,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_531])).

tff(c_578,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_586,plain,(
    ! [D_474,A_475,B_476] :
      ( r2_hidden(D_474,k4_xboole_0(A_475,B_476))
      | r2_hidden(D_474,B_476)
      | ~ r2_hidden(D_474,A_475) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_579,plain,(
    '#skF_10' != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_316])).

tff(c_32,plain,
    ( ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | '#skF_10' = '#skF_8'
    | ~ r2_hidden('#skF_8','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_584,plain,
    ( ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7')))
    | '#skF_10' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_313,c_32])).

tff(c_585,plain,(
    ~ r2_hidden('#skF_5',k4_xboole_0('#skF_6',k1_tarski('#skF_7'))) ),
    inference(negUnitSimplification,[status(thm)],[c_579,c_584])).

tff(c_589,plain,
    ( r2_hidden('#skF_5',k1_tarski('#skF_7'))
    | ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_586,c_585])).

tff(c_598,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_578,c_589])).

tff(c_603,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_598,c_20])).

tff(c_607,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_314,c_603])).

tff(c_608,plain,(
    '#skF_10' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_609,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_312])).

tff(c_620,plain,(
    r2_hidden('#skF_8',k4_xboole_0('#skF_9',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_608,c_609,c_40])).

tff(c_626,plain,(
    ! [D_480,B_481,A_482] :
      ( ~ r2_hidden(D_480,B_481)
      | ~ r2_hidden(D_480,k4_xboole_0(A_482,B_481)) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_629,plain,(
    ~ r2_hidden('#skF_8',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_620,c_626])).

tff(c_633,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_629])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 09:54:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.28/1.42  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.42  
% 2.28/1.42  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.42  %$ r2_hidden > k4_xboole_0 > #nlpp > k1_tarski > #skF_1 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4
% 2.28/1.42  
% 2.28/1.42  %Foreground sorts:
% 2.28/1.42  
% 2.28/1.42  
% 2.28/1.42  %Background operators:
% 2.28/1.42  
% 2.28/1.42  
% 2.28/1.42  %Foreground operators:
% 2.28/1.42  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 2.28/1.42  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.28/1.42  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.28/1.42  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.28/1.42  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.28/1.42  tff('#skF_7', type, '#skF_7': $i).
% 2.28/1.42  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 2.28/1.42  tff('#skF_10', type, '#skF_10': $i).
% 2.28/1.42  tff('#skF_5', type, '#skF_5': $i).
% 2.28/1.42  tff('#skF_6', type, '#skF_6': $i).
% 2.28/1.42  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 2.28/1.42  tff('#skF_9', type, '#skF_9': $i).
% 2.28/1.42  tff('#skF_8', type, '#skF_8': $i).
% 2.28/1.42  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.28/1.42  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.28/1.42  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 2.28/1.42  
% 2.28/1.44  tff(f_42, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 2.28/1.44  tff(f_50, negated_conjecture, ~(![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.28/1.44  tff(f_35, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 2.28/1.44  tff(c_22, plain, (![C_11]: (r2_hidden(C_11, k1_tarski(C_11)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.28/1.44  tff(c_34, plain, ('#skF_7'!='#skF_5' | '#skF_10'='#skF_8' | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.44  tff(c_50, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_34])).
% 2.28/1.44  tff(c_40, plain, ('#skF_7'!='#skF_5' | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.44  tff(c_52, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_40])).
% 2.28/1.44  tff(c_42, plain, (r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.44  tff(c_54, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(splitLeft, [status(thm)], [c_42])).
% 2.28/1.44  tff(c_6, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, A_1) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.28/1.44  tff(c_60, plain, (r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_54, c_6])).
% 2.28/1.44  tff(c_65, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_60])).
% 2.28/1.44  tff(c_66, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_42])).
% 2.28/1.44  tff(c_2, plain, (![D_6, A_1, B_2]: (r2_hidden(D_6, k4_xboole_0(A_1, B_2)) | r2_hidden(D_6, B_2) | ~r2_hidden(D_6, A_1))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.28/1.44  tff(c_67, plain, (~r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_42])).
% 2.28/1.44  tff(c_38, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7'))) | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.44  tff(c_238, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_67, c_38])).
% 2.28/1.44  tff(c_241, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7')) | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_2, c_238])).
% 2.28/1.44  tff(c_249, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_241])).
% 2.28/1.44  tff(c_20, plain, (![C_11, A_7]: (C_11=A_7 | ~r2_hidden(C_11, k1_tarski(A_7)))), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.28/1.44  tff(c_252, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_249, c_20])).
% 2.28/1.44  tff(c_298, plain, $false, inference(negUnitSimplification, [status(thm)], [c_52, c_252])).
% 2.28/1.44  tff(c_299, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_10')))), inference(splitRight, [status(thm)], [c_40])).
% 2.28/1.44  tff(c_307, plain, (r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_299, c_6])).
% 2.28/1.44  tff(c_311, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_307])).
% 2.28/1.44  tff(c_312, plain, ('#skF_7'!='#skF_5' | '#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_34])).
% 2.28/1.44  tff(c_314, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_312])).
% 2.28/1.44  tff(c_313, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_34])).
% 2.28/1.44  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_6') | '#skF_10'='#skF_8' | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.44  tff(c_316, plain, (r2_hidden('#skF_5', '#skF_6') | '#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_313, c_36])).
% 2.28/1.44  tff(c_317, plain, ('#skF_10'='#skF_8'), inference(splitLeft, [status(thm)], [c_316])).
% 2.28/1.44  tff(c_325, plain, (r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_42])).
% 2.28/1.44  tff(c_326, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_325])).
% 2.28/1.44  tff(c_4, plain, (![D_6, B_2, A_1]: (~r2_hidden(D_6, B_2) | ~r2_hidden(D_6, k4_xboole_0(A_1, B_2)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.28/1.44  tff(c_332, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_326, c_4])).
% 2.28/1.44  tff(c_338, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_332])).
% 2.28/1.44  tff(c_339, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_325])).
% 2.28/1.44  tff(c_340, plain, (~r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_325])).
% 2.28/1.44  tff(c_516, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7'))) | r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_317, c_38])).
% 2.28/1.44  tff(c_517, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_340, c_516])).
% 2.28/1.44  tff(c_520, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7')) | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_2, c_517])).
% 2.28/1.44  tff(c_528, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_339, c_520])).
% 2.28/1.44  tff(c_531, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_528, c_20])).
% 2.28/1.44  tff(c_577, plain, $false, inference(negUnitSimplification, [status(thm)], [c_314, c_531])).
% 2.28/1.44  tff(c_578, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_316])).
% 2.28/1.44  tff(c_586, plain, (![D_474, A_475, B_476]: (r2_hidden(D_474, k4_xboole_0(A_475, B_476)) | r2_hidden(D_474, B_476) | ~r2_hidden(D_474, A_475))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.28/1.44  tff(c_579, plain, ('#skF_10'!='#skF_8'), inference(splitRight, [status(thm)], [c_316])).
% 2.28/1.44  tff(c_32, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7'))) | '#skF_10'='#skF_8' | ~r2_hidden('#skF_8', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.28/1.44  tff(c_584, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7'))) | '#skF_10'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_313, c_32])).
% 2.28/1.44  tff(c_585, plain, (~r2_hidden('#skF_5', k4_xboole_0('#skF_6', k1_tarski('#skF_7')))), inference(negUnitSimplification, [status(thm)], [c_579, c_584])).
% 2.28/1.44  tff(c_589, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7')) | ~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_586, c_585])).
% 2.28/1.44  tff(c_598, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_578, c_589])).
% 2.28/1.44  tff(c_603, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_598, c_20])).
% 2.28/1.44  tff(c_607, plain, $false, inference(negUnitSimplification, [status(thm)], [c_314, c_603])).
% 2.28/1.44  tff(c_608, plain, ('#skF_10'='#skF_8'), inference(splitRight, [status(thm)], [c_312])).
% 2.28/1.44  tff(c_609, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_312])).
% 2.28/1.44  tff(c_620, plain, (r2_hidden('#skF_8', k4_xboole_0('#skF_9', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_608, c_609, c_40])).
% 2.28/1.44  tff(c_626, plain, (![D_480, B_481, A_482]: (~r2_hidden(D_480, B_481) | ~r2_hidden(D_480, k4_xboole_0(A_482, B_481)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 2.28/1.44  tff(c_629, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_620, c_626])).
% 2.28/1.44  tff(c_633, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_22, c_629])).
% 2.28/1.44  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.28/1.44  
% 2.28/1.44  Inference rules
% 2.28/1.44  ----------------------
% 2.28/1.44  #Ref     : 0
% 2.28/1.44  #Sup     : 88
% 2.28/1.44  #Fact    : 0
% 2.28/1.44  #Define  : 0
% 2.28/1.44  #Split   : 6
% 2.28/1.44  #Chain   : 0
% 2.28/1.44  #Close   : 0
% 2.28/1.44  
% 2.28/1.44  Ordering : KBO
% 2.28/1.44  
% 2.28/1.44  Simplification rules
% 2.28/1.44  ----------------------
% 2.28/1.44  #Subsume      : 6
% 2.28/1.44  #Demod        : 28
% 2.28/1.44  #Tautology    : 24
% 2.28/1.44  #SimpNegUnit  : 8
% 2.28/1.44  #BackRed      : 0
% 2.28/1.44  
% 2.28/1.44  #Partial instantiations: 372
% 2.28/1.44  #Strategies tried      : 1
% 2.28/1.44  
% 2.28/1.44  Timing (in seconds)
% 2.28/1.44  ----------------------
% 2.28/1.44  Preprocessing        : 0.35
% 2.28/1.44  Parsing              : 0.16
% 2.28/1.44  CNF conversion       : 0.03
% 2.28/1.44  Main loop            : 0.26
% 2.28/1.44  Inferencing          : 0.12
% 2.28/1.44  Reduction            : 0.06
% 2.28/1.44  Demodulation         : 0.04
% 2.28/1.44  BG Simplification    : 0.02
% 2.28/1.44  Subsumption          : 0.04
% 2.28/1.44  Abstraction          : 0.01
% 2.28/1.44  MUC search           : 0.00
% 2.28/1.44  Cooper               : 0.00
% 2.28/1.44  Total                : 0.64
% 2.28/1.44  Index Insertion      : 0.00
% 2.28/1.44  Index Deletion       : 0.00
% 2.28/1.44  Index Matching       : 0.00
% 2.28/1.44  BG Taut test         : 0.00
%------------------------------------------------------------------------------

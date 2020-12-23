%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:52 EST 2020

% Result     : Theorem 3.32s
% Output     : CNFRefutation 3.36s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 163 expanded)
%              Number of leaves         :   24 (  64 expanded)
%              Depth                    :    8
%              Number of atoms          :   87 ( 299 expanded)
%              Number of equality atoms :   31 ( 172 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_1 > #skF_12 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_11',type,(
    '#skF_11': $i )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

tff('#skF_10',type,(
    '#skF_10': $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_9',type,(
    '#skF_9': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff('#skF_12',type,(
    '#skF_12': $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_47,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(f_57,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
      <=> ( A = C
          & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(c_28,plain,(
    ! [C_12] : r2_hidden(C_12,k1_tarski(C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_1653,plain,(
    ! [A_2168,B_2169,C_2170,D_2171] :
      ( r2_hidden(k4_tarski(A_2168,B_2169),k2_zfmisc_1(C_2170,D_2171))
      | ~ r2_hidden(B_2169,D_2171)
      | ~ r2_hidden(A_2168,C_2170) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_615,plain,(
    ! [A_776,B_777,C_778,D_779] :
      ( r2_hidden(k4_tarski(A_776,B_777),k2_zfmisc_1(C_778,D_779))
      | ~ r2_hidden(B_777,D_779)
      | ~ r2_hidden(A_776,C_778) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_52,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_10' != '#skF_12'
    | '#skF_11' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_69,plain,(
    '#skF_11' != '#skF_9' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,
    ( '#skF_7' = '#skF_5'
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),k1_tarski('#skF_12'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_79,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),k1_tarski('#skF_12'))) ),
    inference(splitLeft,[status(thm)],[c_58])).

tff(c_109,plain,(
    ! [A_39,C_40,B_41,D_42] :
      ( r2_hidden(A_39,C_40)
      | ~ r2_hidden(k4_tarski(A_39,B_41),k2_zfmisc_1(C_40,D_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_113,plain,(
    r2_hidden('#skF_9',k1_tarski('#skF_11')) ),
    inference(resolution,[status(thm)],[c_79,c_109])).

tff(c_26,plain,(
    ! [C_12,A_8] :
      ( C_12 = A_8
      | ~ r2_hidden(C_12,k1_tarski(A_8)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_116,plain,(
    '#skF_11' = '#skF_9' ),
    inference(resolution,[status(thm)],[c_113,c_26])).

tff(c_120,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_69,c_116])).

tff(c_122,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),k1_tarski('#skF_12'))) ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_56,plain,
    ( '#skF_6' = '#skF_8'
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),k1_tarski('#skF_12'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_145,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),k1_tarski('#skF_12'))) ),
    inference(splitLeft,[status(thm)],[c_56])).

tff(c_158,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_145,c_122])).

tff(c_159,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_56])).

tff(c_121,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_58])).

tff(c_54,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8')))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),k1_tarski('#skF_12'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_440,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8')))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_11'),k1_tarski('#skF_12'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_121,c_54])).

tff(c_441,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_122,c_440])).

tff(c_622,plain,
    ( ~ r2_hidden('#skF_8',k1_tarski('#skF_8'))
    | ~ r2_hidden('#skF_5',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_615,c_441])).

tff(c_638,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_622])).

tff(c_640,plain,(
    '#skF_11' = '#skF_9' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_1165,plain,(
    ! [A_1504,B_1505,C_1506,D_1507] :
      ( r2_hidden(k4_tarski(A_1504,B_1505),k2_zfmisc_1(C_1506,D_1507))
      | ~ r2_hidden(B_1505,D_1507)
      | ~ r2_hidden(A_1504,C_1506) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_712,plain,
    ( '#skF_7' = '#skF_5'
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_12'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_58])).

tff(c_713,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_12'))) ),
    inference(splitLeft,[status(thm)],[c_712])).

tff(c_639,plain,
    ( '#skF_10' != '#skF_12'
    | '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_645,plain,(
    '#skF_10' != '#skF_12' ),
    inference(splitLeft,[status(thm)],[c_639])).

tff(c_657,plain,
    ( '#skF_6' = '#skF_8'
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_12'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_56])).

tff(c_658,plain,(
    r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_12'))) ),
    inference(splitLeft,[status(thm)],[c_657])).

tff(c_694,plain,(
    ! [B_823,D_824,A_825,C_826] :
      ( r2_hidden(B_823,D_824)
      | ~ r2_hidden(k4_tarski(A_825,B_823),k2_zfmisc_1(C_826,D_824)) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_698,plain,(
    r2_hidden('#skF_10',k1_tarski('#skF_12')) ),
    inference(resolution,[status(thm)],[c_658,c_694])).

tff(c_701,plain,(
    '#skF_10' = '#skF_12' ),
    inference(resolution,[status(thm)],[c_698,c_26])).

tff(c_705,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_645,c_701])).

tff(c_707,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_12'))) ),
    inference(splitRight,[status(thm)],[c_657])).

tff(c_744,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_713,c_707])).

tff(c_746,plain,(
    ~ r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_12'))) ),
    inference(splitRight,[status(thm)],[c_712])).

tff(c_745,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_712])).

tff(c_706,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_657])).

tff(c_1027,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8')))
    | r2_hidden(k4_tarski('#skF_9','#skF_10'),k2_zfmisc_1(k1_tarski('#skF_9'),k1_tarski('#skF_12'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_745,c_706,c_54])).

tff(c_1028,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(negUnitSimplification,[status(thm)],[c_746,c_1027])).

tff(c_1172,plain,
    ( ~ r2_hidden('#skF_8',k1_tarski('#skF_8'))
    | ~ r2_hidden('#skF_5',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1165,c_1028])).

tff(c_1190,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_1172])).

tff(c_1192,plain,(
    '#skF_10' = '#skF_12' ),
    inference(splitRight,[status(thm)],[c_639])).

tff(c_50,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_10' != '#skF_12'
    | '#skF_11' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1210,plain,(
    '#skF_6' = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_1192,c_50])).

tff(c_1191,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_639])).

tff(c_48,plain,
    ( ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8')))
    | '#skF_10' != '#skF_12'
    | '#skF_11' != '#skF_9' ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1485,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_8'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_1192,c_1210,c_1191,c_48])).

tff(c_1656,plain,
    ( ~ r2_hidden('#skF_8',k1_tarski('#skF_8'))
    | ~ r2_hidden('#skF_5',k1_tarski('#skF_5')) ),
    inference(resolution,[status(thm)],[c_1653,c_1485])).

tff(c_1668,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_28,c_1656])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 19:44:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.32/1.52  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.53  
% 3.36/1.53  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.53  %$ r2_hidden > k1_enumset1 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_11 > #skF_7 > #skF_3 > #skF_10 > #skF_5 > #skF_2 > #skF_6 > #skF_9 > #skF_8 > #skF_1 > #skF_12 > #skF_4
% 3.36/1.53  
% 3.36/1.53  %Foreground sorts:
% 3.36/1.53  
% 3.36/1.53  
% 3.36/1.53  %Background operators:
% 3.36/1.53  
% 3.36/1.53  
% 3.36/1.53  %Foreground operators:
% 3.36/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.36/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.36/1.53  tff('#skF_11', type, '#skF_11': $i).
% 3.36/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.36/1.53  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 3.36/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.36/1.53  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.36/1.53  tff('#skF_10', type, '#skF_10': $i).
% 3.36/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.36/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.36/1.53  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.36/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.36/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.36/1.53  tff('#skF_9', type, '#skF_9': $i).
% 3.36/1.53  tff('#skF_8', type, '#skF_8': $i).
% 3.36/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.36/1.53  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 3.36/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.36/1.53  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.36/1.53  tff('#skF_12', type, '#skF_12': $i).
% 3.36/1.53  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.36/1.53  
% 3.36/1.54  tff(f_47, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 3.36/1.54  tff(f_57, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.36/1.54  tff(f_64, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 3.36/1.54  tff(c_28, plain, (![C_12]: (r2_hidden(C_12, k1_tarski(C_12)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.54  tff(c_1653, plain, (![A_2168, B_2169, C_2170, D_2171]: (r2_hidden(k4_tarski(A_2168, B_2169), k2_zfmisc_1(C_2170, D_2171)) | ~r2_hidden(B_2169, D_2171) | ~r2_hidden(A_2168, C_2170))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.36/1.54  tff(c_615, plain, (![A_776, B_777, C_778, D_779]: (r2_hidden(k4_tarski(A_776, B_777), k2_zfmisc_1(C_778, D_779)) | ~r2_hidden(B_777, D_779) | ~r2_hidden(A_776, C_778))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.36/1.54  tff(c_52, plain, ('#skF_7'='#skF_5' | '#skF_10'!='#skF_12' | '#skF_11'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.36/1.54  tff(c_69, plain, ('#skF_11'!='#skF_9'), inference(splitLeft, [status(thm)], [c_52])).
% 3.36/1.54  tff(c_58, plain, ('#skF_7'='#skF_5' | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), k1_tarski('#skF_12')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.36/1.54  tff(c_79, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), k1_tarski('#skF_12')))), inference(splitLeft, [status(thm)], [c_58])).
% 3.36/1.54  tff(c_109, plain, (![A_39, C_40, B_41, D_42]: (r2_hidden(A_39, C_40) | ~r2_hidden(k4_tarski(A_39, B_41), k2_zfmisc_1(C_40, D_42)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.36/1.54  tff(c_113, plain, (r2_hidden('#skF_9', k1_tarski('#skF_11'))), inference(resolution, [status(thm)], [c_79, c_109])).
% 3.36/1.54  tff(c_26, plain, (![C_12, A_8]: (C_12=A_8 | ~r2_hidden(C_12, k1_tarski(A_8)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.36/1.54  tff(c_116, plain, ('#skF_11'='#skF_9'), inference(resolution, [status(thm)], [c_113, c_26])).
% 3.36/1.54  tff(c_120, plain, $false, inference(negUnitSimplification, [status(thm)], [c_69, c_116])).
% 3.36/1.54  tff(c_122, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), k1_tarski('#skF_12')))), inference(splitRight, [status(thm)], [c_58])).
% 3.36/1.54  tff(c_56, plain, ('#skF_6'='#skF_8' | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), k1_tarski('#skF_12')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.36/1.54  tff(c_145, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), k1_tarski('#skF_12')))), inference(splitLeft, [status(thm)], [c_56])).
% 3.36/1.54  tff(c_158, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_145, c_122])).
% 3.36/1.54  tff(c_159, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_56])).
% 3.36/1.54  tff(c_121, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_58])).
% 3.36/1.54  tff(c_54, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8'))) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), k1_tarski('#skF_12')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.36/1.54  tff(c_440, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8'))) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_11'), k1_tarski('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_159, c_121, c_54])).
% 3.36/1.54  tff(c_441, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_122, c_440])).
% 3.36/1.54  tff(c_622, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8')) | ~r2_hidden('#skF_5', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_615, c_441])).
% 3.36/1.54  tff(c_638, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_622])).
% 3.36/1.54  tff(c_640, plain, ('#skF_11'='#skF_9'), inference(splitRight, [status(thm)], [c_52])).
% 3.36/1.54  tff(c_1165, plain, (![A_1504, B_1505, C_1506, D_1507]: (r2_hidden(k4_tarski(A_1504, B_1505), k2_zfmisc_1(C_1506, D_1507)) | ~r2_hidden(B_1505, D_1507) | ~r2_hidden(A_1504, C_1506))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.36/1.54  tff(c_712, plain, ('#skF_7'='#skF_5' | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_640, c_58])).
% 3.36/1.54  tff(c_713, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_12')))), inference(splitLeft, [status(thm)], [c_712])).
% 3.36/1.54  tff(c_639, plain, ('#skF_10'!='#skF_12' | '#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_52])).
% 3.36/1.54  tff(c_645, plain, ('#skF_10'!='#skF_12'), inference(splitLeft, [status(thm)], [c_639])).
% 3.36/1.54  tff(c_657, plain, ('#skF_6'='#skF_8' | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_640, c_56])).
% 3.36/1.54  tff(c_658, plain, (r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_12')))), inference(splitLeft, [status(thm)], [c_657])).
% 3.36/1.54  tff(c_694, plain, (![B_823, D_824, A_825, C_826]: (r2_hidden(B_823, D_824) | ~r2_hidden(k4_tarski(A_825, B_823), k2_zfmisc_1(C_826, D_824)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.36/1.54  tff(c_698, plain, (r2_hidden('#skF_10', k1_tarski('#skF_12'))), inference(resolution, [status(thm)], [c_658, c_694])).
% 3.36/1.54  tff(c_701, plain, ('#skF_10'='#skF_12'), inference(resolution, [status(thm)], [c_698, c_26])).
% 3.36/1.54  tff(c_705, plain, $false, inference(negUnitSimplification, [status(thm)], [c_645, c_701])).
% 3.36/1.54  tff(c_707, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_12')))), inference(splitRight, [status(thm)], [c_657])).
% 3.36/1.54  tff(c_744, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_713, c_707])).
% 3.36/1.54  tff(c_746, plain, (~r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_12')))), inference(splitRight, [status(thm)], [c_712])).
% 3.36/1.54  tff(c_745, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_712])).
% 3.36/1.54  tff(c_706, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_657])).
% 3.36/1.54  tff(c_1027, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8'))) | r2_hidden(k4_tarski('#skF_9', '#skF_10'), k2_zfmisc_1(k1_tarski('#skF_9'), k1_tarski('#skF_12')))), inference(demodulation, [status(thm), theory('equality')], [c_640, c_745, c_706, c_54])).
% 3.36/1.54  tff(c_1028, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(negUnitSimplification, [status(thm)], [c_746, c_1027])).
% 3.36/1.54  tff(c_1172, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8')) | ~r2_hidden('#skF_5', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_1165, c_1028])).
% 3.36/1.54  tff(c_1190, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_1172])).
% 3.36/1.54  tff(c_1192, plain, ('#skF_10'='#skF_12'), inference(splitRight, [status(thm)], [c_639])).
% 3.36/1.54  tff(c_50, plain, ('#skF_6'='#skF_8' | '#skF_10'!='#skF_12' | '#skF_11'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.36/1.54  tff(c_1210, plain, ('#skF_6'='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_640, c_1192, c_50])).
% 3.36/1.54  tff(c_1191, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_639])).
% 3.36/1.54  tff(c_48, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8'))) | '#skF_10'!='#skF_12' | '#skF_11'!='#skF_9'), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.36/1.54  tff(c_1485, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_8'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_640, c_1192, c_1210, c_1191, c_48])).
% 3.36/1.54  tff(c_1656, plain, (~r2_hidden('#skF_8', k1_tarski('#skF_8')) | ~r2_hidden('#skF_5', k1_tarski('#skF_5'))), inference(resolution, [status(thm)], [c_1653, c_1485])).
% 3.36/1.54  tff(c_1668, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_28, c_1656])).
% 3.36/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.36/1.54  
% 3.36/1.54  Inference rules
% 3.36/1.54  ----------------------
% 3.36/1.54  #Ref     : 0
% 3.36/1.54  #Sup     : 236
% 3.36/1.54  #Fact    : 0
% 3.36/1.54  #Define  : 0
% 3.36/1.54  #Split   : 6
% 3.36/1.54  #Chain   : 0
% 3.36/1.54  #Close   : 0
% 3.36/1.54  
% 3.36/1.54  Ordering : KBO
% 3.36/1.54  
% 3.36/1.54  Simplification rules
% 3.36/1.54  ----------------------
% 3.36/1.54  #Subsume      : 19
% 3.36/1.54  #Demod        : 141
% 3.36/1.54  #Tautology    : 78
% 3.36/1.54  #SimpNegUnit  : 4
% 3.36/1.54  #BackRed      : 0
% 3.36/1.54  
% 3.36/1.54  #Partial instantiations: 1513
% 3.36/1.54  #Strategies tried      : 1
% 3.36/1.54  
% 3.36/1.54  Timing (in seconds)
% 3.36/1.54  ----------------------
% 3.36/1.55  Preprocessing        : 0.31
% 3.36/1.55  Parsing              : 0.15
% 3.36/1.55  CNF conversion       : 0.03
% 3.36/1.55  Main loop            : 0.47
% 3.36/1.55  Inferencing          : 0.23
% 3.36/1.55  Reduction            : 0.12
% 3.36/1.55  Demodulation         : 0.08
% 3.36/1.55  BG Simplification    : 0.03
% 3.36/1.55  Subsumption          : 0.07
% 3.36/1.55  Abstraction          : 0.02
% 3.36/1.55  MUC search           : 0.00
% 3.36/1.55  Cooper               : 0.00
% 3.36/1.55  Total                : 0.81
% 3.36/1.55  Index Insertion      : 0.00
% 3.36/1.55  Index Deletion       : 0.00
% 3.36/1.55  Index Matching       : 0.00
% 3.36/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------

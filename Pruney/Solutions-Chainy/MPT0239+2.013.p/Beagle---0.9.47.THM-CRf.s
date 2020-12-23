%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:53 EST 2020

% Result     : Theorem 2.05s
% Output     : CNFRefutation 2.05s
% Verified   : 
% Statistics : Number of formulae       :   92 ( 218 expanded)
%              Number of leaves         :   24 (  80 expanded)
%              Depth                    :    8
%              Number of atoms          :  116 ( 400 expanded)
%              Number of equality atoms :   50 ( 246 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4

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

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(f_27,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ( k4_xboole_0(k2_tarski(A,B),C) = k1_tarski(A)
    <=> ( ~ r2_hidden(A,C)
        & ( r2_hidden(B,C)
          | A = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l38_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_58,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
      <=> ( A = C
          & B = D ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(c_2,plain,(
    ! [A_1] : k2_tarski(A_1,A_1) = k1_tarski(A_1) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [B_8,C_9] :
      ( k4_xboole_0(k2_tarski(B_8,B_8),C_9) = k1_tarski(B_8)
      | r2_hidden(B_8,C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_514,plain,(
    ! [B_136,C_137] :
      ( k4_xboole_0(k1_tarski(B_136),C_137) = k1_tarski(B_136)
      | r2_hidden(B_136,C_137) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_22,plain,(
    ! [B_15] : k4_xboole_0(k1_tarski(B_15),k1_tarski(B_15)) != k1_tarski(B_15) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_534,plain,(
    ! [B_136] : r2_hidden(B_136,k1_tarski(B_136)) ),
    inference(superposition,[status(thm),theory(equality)],[c_514,c_22])).

tff(c_577,plain,(
    ! [A_160,B_161,C_162,D_163] :
      ( r2_hidden(k4_tarski(A_160,B_161),k2_zfmisc_1(C_162,D_163))
      | ~ r2_hidden(B_161,D_163)
      | ~ r2_hidden(A_160,C_162) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_74,plain,(
    ! [B_22,C_23] :
      ( k4_xboole_0(k1_tarski(B_22),C_23) = k1_tarski(B_22)
      | r2_hidden(B_22,C_23) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_94,plain,(
    ! [B_22] : r2_hidden(B_22,k1_tarski(B_22)) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_22])).

tff(c_16,plain,(
    ! [A_10,B_11,C_12,D_13] :
      ( r2_hidden(k4_tarski(A_10,B_11),k2_zfmisc_1(C_12,D_13))
      | ~ r2_hidden(B_11,D_13)
      | ~ r2_hidden(A_10,C_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_30,plain,
    ( '#skF_3' = '#skF_1'
    | '#skF_6' != '#skF_8'
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_47,plain,(
    '#skF_7' != '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_34,plain,
    ( '#skF_2' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_98,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_108,plain,(
    ! [A_28,C_29,B_30,D_31] :
      ( r2_hidden(A_28,C_29)
      | ~ r2_hidden(k4_tarski(A_28,B_30),k2_zfmisc_1(C_29,D_31)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_112,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(resolution,[status(thm)],[c_98,c_108])).

tff(c_24,plain,(
    ! [A_14,B_15] :
      ( k4_xboole_0(k1_tarski(A_14),k1_tarski(B_15)) = k1_tarski(A_14)
      | B_15 = A_14 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_113,plain,(
    ! [A_32,C_33,B_34] :
      ( ~ r2_hidden(A_32,C_33)
      | k4_xboole_0(k2_tarski(A_32,B_34),C_33) != k1_tarski(A_32) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_122,plain,(
    ! [A_39,C_40] :
      ( ~ r2_hidden(A_39,C_40)
      | k4_xboole_0(k1_tarski(A_39),C_40) != k1_tarski(A_39) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_113])).

tff(c_131,plain,(
    ! [A_41,B_42] :
      ( ~ r2_hidden(A_41,k1_tarski(B_42))
      | B_42 = A_41 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_122])).

tff(c_137,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_112,c_131])).

tff(c_145,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_47,c_137])).

tff(c_147,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36,plain,
    ( '#skF_3' = '#skF_1'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_148,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_162,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_147,c_148])).

tff(c_164,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_163,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_146,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_32,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_243,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_7'),k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_163,c_146,c_32])).

tff(c_244,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_164,c_243])).

tff(c_247,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_244])).

tff(c_251,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_94,c_94,c_247])).

tff(c_253,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_287,plain,(
    ! [B_79,C_80] :
      ( k4_xboole_0(k1_tarski(B_79),C_80) = k1_tarski(B_79)
      | r2_hidden(B_79,C_80) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_12])).

tff(c_307,plain,(
    ! [B_79] : r2_hidden(B_79,k1_tarski(B_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_287,c_22])).

tff(c_252,plain,
    ( '#skF_6' != '#skF_8'
    | '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_258,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_252])).

tff(c_311,plain,
    ( '#skF_2' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_34])).

tff(c_312,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_311])).

tff(c_341,plain,(
    ! [B_94,D_95,A_96,C_97] :
      ( r2_hidden(B_94,D_95)
      | ~ r2_hidden(k4_tarski(A_96,B_94),k2_zfmisc_1(C_97,D_95)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_345,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_312,c_341])).

tff(c_328,plain,(
    ! [A_89,C_90,B_91] :
      ( ~ r2_hidden(A_89,C_90)
      | k4_xboole_0(k2_tarski(A_89,B_91),C_90) != k1_tarski(A_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_332,plain,(
    ! [A_92,C_93] :
      ( ~ r2_hidden(A_92,C_93)
      | k4_xboole_0(k1_tarski(A_92),C_93) != k1_tarski(A_92) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_328])).

tff(c_346,plain,(
    ! [A_98,B_99] :
      ( ~ r2_hidden(A_98,k1_tarski(B_99))
      | B_99 = A_98 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_332])).

tff(c_349,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_345,c_346])).

tff(c_356,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_258,c_349])).

tff(c_358,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_311])).

tff(c_363,plain,
    ( '#skF_3' = '#skF_1'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_36])).

tff(c_364,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_363])).

tff(c_374,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_358,c_364])).

tff(c_375,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_363])).

tff(c_357,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_311])).

tff(c_453,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1(k1_tarski('#skF_5'),k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_375,c_357,c_32])).

tff(c_454,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_358,c_453])).

tff(c_457,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_16,c_454])).

tff(c_461,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_307,c_307,c_457])).

tff(c_463,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_28,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_6' != '#skF_8'
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_469,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_6' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_28])).

tff(c_470,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_469])).

tff(c_476,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_463,c_470])).

tff(c_477,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_469])).

tff(c_462,plain,(
    '#skF_3' = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_252])).

tff(c_26,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1(k1_tarski('#skF_3'),k1_tarski('#skF_4')))
    | '#skF_6' != '#skF_8'
    | '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_576,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1(k1_tarski('#skF_1'),k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_253,c_463,c_477,c_462,c_26])).

tff(c_580,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1',k1_tarski('#skF_1')) ),
    inference(resolution,[status(thm)],[c_577,c_576])).

tff(c_590,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_534,c_534,c_580])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n018.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 18:03:42 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.05/1.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.30  
% 2.05/1.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.30  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.05/1.30  
% 2.05/1.30  %Foreground sorts:
% 2.05/1.30  
% 2.05/1.30  
% 2.05/1.30  %Background operators:
% 2.05/1.30  
% 2.05/1.30  
% 2.05/1.30  %Foreground operators:
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.05/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.05/1.30  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.05/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.05/1.30  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.05/1.30  tff('#skF_7', type, '#skF_7': $i).
% 2.05/1.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.05/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.05/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.05/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.05/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.05/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.05/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.05/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.05/1.30  tff('#skF_8', type, '#skF_8': $i).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.05/1.30  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.05/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.05/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.05/1.30  
% 2.05/1.32  tff(f_27, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 2.05/1.32  tff(f_40, axiom, (![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k1_tarski(A)) <=> (~r2_hidden(A, C) & (r2_hidden(B, C) | (A = B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l38_zfmisc_1)).
% 2.05/1.32  tff(f_51, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.05/1.32  tff(f_46, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.05/1.32  tff(f_58, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 2.05/1.32  tff(c_2, plain, (![A_1]: (k2_tarski(A_1, A_1)=k1_tarski(A_1))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.05/1.32  tff(c_12, plain, (![B_8, C_9]: (k4_xboole_0(k2_tarski(B_8, B_8), C_9)=k1_tarski(B_8) | r2_hidden(B_8, C_9))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.05/1.32  tff(c_514, plain, (![B_136, C_137]: (k4_xboole_0(k1_tarski(B_136), C_137)=k1_tarski(B_136) | r2_hidden(B_136, C_137))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 2.05/1.32  tff(c_22, plain, (![B_15]: (k4_xboole_0(k1_tarski(B_15), k1_tarski(B_15))!=k1_tarski(B_15))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.32  tff(c_534, plain, (![B_136]: (r2_hidden(B_136, k1_tarski(B_136)))), inference(superposition, [status(thm), theory('equality')], [c_514, c_22])).
% 2.05/1.32  tff(c_577, plain, (![A_160, B_161, C_162, D_163]: (r2_hidden(k4_tarski(A_160, B_161), k2_zfmisc_1(C_162, D_163)) | ~r2_hidden(B_161, D_163) | ~r2_hidden(A_160, C_162))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.05/1.32  tff(c_74, plain, (![B_22, C_23]: (k4_xboole_0(k1_tarski(B_22), C_23)=k1_tarski(B_22) | r2_hidden(B_22, C_23))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 2.05/1.32  tff(c_94, plain, (![B_22]: (r2_hidden(B_22, k1_tarski(B_22)))), inference(superposition, [status(thm), theory('equality')], [c_74, c_22])).
% 2.05/1.32  tff(c_16, plain, (![A_10, B_11, C_12, D_13]: (r2_hidden(k4_tarski(A_10, B_11), k2_zfmisc_1(C_12, D_13)) | ~r2_hidden(B_11, D_13) | ~r2_hidden(A_10, C_12))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.05/1.32  tff(c_30, plain, ('#skF_3'='#skF_1' | '#skF_6'!='#skF_8' | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.32  tff(c_47, plain, ('#skF_7'!='#skF_5'), inference(splitLeft, [status(thm)], [c_30])).
% 2.05/1.32  tff(c_34, plain, ('#skF_2'='#skF_4' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.32  tff(c_98, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_34])).
% 2.05/1.32  tff(c_108, plain, (![A_28, C_29, B_30, D_31]: (r2_hidden(A_28, C_29) | ~r2_hidden(k4_tarski(A_28, B_30), k2_zfmisc_1(C_29, D_31)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.05/1.32  tff(c_112, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(resolution, [status(thm)], [c_98, c_108])).
% 2.05/1.32  tff(c_24, plain, (![A_14, B_15]: (k4_xboole_0(k1_tarski(A_14), k1_tarski(B_15))=k1_tarski(A_14) | B_15=A_14)), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.05/1.32  tff(c_113, plain, (![A_32, C_33, B_34]: (~r2_hidden(A_32, C_33) | k4_xboole_0(k2_tarski(A_32, B_34), C_33)!=k1_tarski(A_32))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.05/1.32  tff(c_122, plain, (![A_39, C_40]: (~r2_hidden(A_39, C_40) | k4_xboole_0(k1_tarski(A_39), C_40)!=k1_tarski(A_39))), inference(superposition, [status(thm), theory('equality')], [c_2, c_113])).
% 2.05/1.32  tff(c_131, plain, (![A_41, B_42]: (~r2_hidden(A_41, k1_tarski(B_42)) | B_42=A_41)), inference(superposition, [status(thm), theory('equality')], [c_24, c_122])).
% 2.05/1.32  tff(c_137, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_112, c_131])).
% 2.05/1.32  tff(c_145, plain, $false, inference(negUnitSimplification, [status(thm)], [c_47, c_137])).
% 2.05/1.32  tff(c_147, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_34])).
% 2.05/1.32  tff(c_36, plain, ('#skF_3'='#skF_1' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.32  tff(c_148, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_36])).
% 2.05/1.32  tff(c_162, plain, $false, inference(negUnitSimplification, [status(thm)], [c_147, c_148])).
% 2.05/1.32  tff(c_164, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_36])).
% 2.05/1.32  tff(c_163, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_36])).
% 2.05/1.32  tff(c_146, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_34])).
% 2.05/1.32  tff(c_32, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.32  tff(c_243, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_7'), k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_163, c_146, c_32])).
% 2.05/1.32  tff(c_244, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_164, c_243])).
% 2.05/1.32  tff(c_247, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_244])).
% 2.05/1.32  tff(c_251, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_94, c_94, c_247])).
% 2.05/1.32  tff(c_253, plain, ('#skF_7'='#skF_5'), inference(splitRight, [status(thm)], [c_30])).
% 2.05/1.32  tff(c_287, plain, (![B_79, C_80]: (k4_xboole_0(k1_tarski(B_79), C_80)=k1_tarski(B_79) | r2_hidden(B_79, C_80))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_12])).
% 2.05/1.32  tff(c_307, plain, (![B_79]: (r2_hidden(B_79, k1_tarski(B_79)))), inference(superposition, [status(thm), theory('equality')], [c_287, c_22])).
% 2.05/1.32  tff(c_252, plain, ('#skF_6'!='#skF_8' | '#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_30])).
% 2.05/1.32  tff(c_258, plain, ('#skF_6'!='#skF_8'), inference(splitLeft, [status(thm)], [c_252])).
% 2.05/1.32  tff(c_311, plain, ('#skF_2'='#skF_4' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_34])).
% 2.05/1.32  tff(c_312, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_311])).
% 2.05/1.32  tff(c_341, plain, (![B_94, D_95, A_96, C_97]: (r2_hidden(B_94, D_95) | ~r2_hidden(k4_tarski(A_96, B_94), k2_zfmisc_1(C_97, D_95)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 2.05/1.32  tff(c_345, plain, (r2_hidden('#skF_6', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_312, c_341])).
% 2.05/1.32  tff(c_328, plain, (![A_89, C_90, B_91]: (~r2_hidden(A_89, C_90) | k4_xboole_0(k2_tarski(A_89, B_91), C_90)!=k1_tarski(A_89))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.05/1.32  tff(c_332, plain, (![A_92, C_93]: (~r2_hidden(A_92, C_93) | k4_xboole_0(k1_tarski(A_92), C_93)!=k1_tarski(A_92))), inference(superposition, [status(thm), theory('equality')], [c_2, c_328])).
% 2.05/1.32  tff(c_346, plain, (![A_98, B_99]: (~r2_hidden(A_98, k1_tarski(B_99)) | B_99=A_98)), inference(superposition, [status(thm), theory('equality')], [c_24, c_332])).
% 2.05/1.32  tff(c_349, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_345, c_346])).
% 2.05/1.32  tff(c_356, plain, $false, inference(negUnitSimplification, [status(thm)], [c_258, c_349])).
% 2.05/1.32  tff(c_358, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_311])).
% 2.05/1.32  tff(c_363, plain, ('#skF_3'='#skF_1' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_36])).
% 2.05/1.32  tff(c_364, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_363])).
% 2.05/1.32  tff(c_374, plain, $false, inference(negUnitSimplification, [status(thm)], [c_358, c_364])).
% 2.05/1.32  tff(c_375, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_363])).
% 2.05/1.32  tff(c_357, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_311])).
% 2.05/1.32  tff(c_453, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1(k1_tarski('#skF_5'), k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_375, c_357, c_32])).
% 2.05/1.32  tff(c_454, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_358, c_453])).
% 2.05/1.32  tff(c_457, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_16, c_454])).
% 2.05/1.32  tff(c_461, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_307, c_307, c_457])).
% 2.05/1.32  tff(c_463, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_252])).
% 2.05/1.32  tff(c_28, plain, ('#skF_2'='#skF_4' | '#skF_6'!='#skF_8' | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.32  tff(c_469, plain, ('#skF_2'='#skF_4' | '#skF_6'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_253, c_28])).
% 2.05/1.32  tff(c_470, plain, ('#skF_6'!='#skF_8'), inference(splitLeft, [status(thm)], [c_469])).
% 2.05/1.32  tff(c_476, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_463, c_470])).
% 2.05/1.32  tff(c_477, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_469])).
% 2.05/1.32  tff(c_462, plain, ('#skF_3'='#skF_1'), inference(splitRight, [status(thm)], [c_252])).
% 2.05/1.32  tff(c_26, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1(k1_tarski('#skF_3'), k1_tarski('#skF_4'))) | '#skF_6'!='#skF_8' | '#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_58])).
% 2.05/1.32  tff(c_576, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1(k1_tarski('#skF_1'), k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_253, c_463, c_477, c_462, c_26])).
% 2.05/1.32  tff(c_580, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', k1_tarski('#skF_1'))), inference(resolution, [status(thm)], [c_577, c_576])).
% 2.05/1.32  tff(c_590, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_534, c_534, c_580])).
% 2.05/1.32  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 2.05/1.32  
% 2.05/1.32  Inference rules
% 2.05/1.32  ----------------------
% 2.05/1.32  #Ref     : 0
% 2.05/1.32  #Sup     : 117
% 2.05/1.32  #Fact    : 0
% 2.05/1.32  #Define  : 0
% 2.05/1.32  #Split   : 8
% 2.05/1.32  #Chain   : 0
% 2.05/1.32  #Close   : 0
% 2.05/1.32  
% 2.05/1.32  Ordering : KBO
% 2.05/1.32  
% 2.05/1.32  Simplification rules
% 2.05/1.32  ----------------------
% 2.05/1.32  #Subsume      : 8
% 2.05/1.32  #Demod        : 35
% 2.05/1.32  #Tautology    : 90
% 2.05/1.32  #SimpNegUnit  : 6
% 2.05/1.32  #BackRed      : 0
% 2.05/1.32  
% 2.05/1.32  #Partial instantiations: 0
% 2.05/1.32  #Strategies tried      : 1
% 2.05/1.32  
% 2.05/1.32  Timing (in seconds)
% 2.05/1.32  ----------------------
% 2.46/1.32  Preprocessing        : 0.29
% 2.46/1.32  Parsing              : 0.15
% 2.46/1.32  CNF conversion       : 0.02
% 2.46/1.32  Main loop            : 0.26
% 2.46/1.32  Inferencing          : 0.11
% 2.46/1.32  Reduction            : 0.07
% 2.46/1.32  Demodulation         : 0.05
% 2.46/1.32  BG Simplification    : 0.02
% 2.46/1.32  Subsumption          : 0.04
% 2.46/1.32  Abstraction          : 0.01
% 2.46/1.32  MUC search           : 0.00
% 2.46/1.32  Cooper               : 0.00
% 2.46/1.32  Total                : 0.59
% 2.46/1.32  Index Insertion      : 0.00
% 2.46/1.32  Index Deletion       : 0.00
% 2.46/1.32  Index Matching       : 0.00
% 2.46/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------

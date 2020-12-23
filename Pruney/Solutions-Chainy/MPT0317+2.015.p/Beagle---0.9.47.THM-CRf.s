%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:01 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   75 ( 129 expanded)
%              Number of leaves         :   24 (  53 expanded)
%              Depth                    :    6
%              Number of atoms          :   91 ( 229 expanded)
%              Number of equality atoms :   22 (  72 expanded)
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

tff(f_62,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,k1_tarski(D)))
      <=> ( r2_hidden(A,C)
          & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t129_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(k1_tarski(C),k1_tarski(D)))
    <=> ( A = C
        & B = D ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t34_zfmisc_1)).

tff(f_42,axiom,(
    ! [A,B] :
      ( k4_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
    <=> A != B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t20_zfmisc_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( r2_hidden(A,k4_xboole_0(B,k1_tarski(C)))
    <=> ( r2_hidden(A,B)
        & A != C ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t64_zfmisc_1)).

tff(c_32,plain,
    ( '#skF_2' = '#skF_4'
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_60,plain,(
    ~ r2_hidden('#skF_5','#skF_7') ),
    inference(splitLeft,[status(thm)],[c_32])).

tff(c_38,plain,
    ( '#skF_2' = '#skF_4'
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_72,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_97,plain,(
    ! [A_38,C_39,B_40,D_41] :
      ( r2_hidden(A_38,C_39)
      | ~ r2_hidden(k4_tarski(A_38,B_40),k2_zfmisc_1(C_39,D_41)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_103,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(resolution,[status(thm)],[c_72,c_97])).

tff(c_108,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_60,c_103])).

tff(c_110,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_40,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_138,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_40])).

tff(c_18,plain,(
    ! [C_15,D_16] : r2_hidden(k4_tarski(C_15,D_16),k2_zfmisc_1(k1_tarski(C_15),k1_tarski(D_16))) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_140,plain,(
    ! [A_48,C_49,B_50,D_51] :
      ( r2_hidden(A_48,C_49)
      | ~ r2_hidden(k4_tarski(A_48,B_50),k2_zfmisc_1(C_49,D_51)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_144,plain,(
    ! [C_15] : r2_hidden(C_15,k1_tarski(C_15)) ),
    inference(resolution,[status(thm)],[c_18,c_140])).

tff(c_8,plain,(
    ! [A_7,B_8,C_9,D_10] :
      ( r2_hidden(k4_tarski(A_7,B_8),k2_zfmisc_1(C_9,D_10))
      | ~ r2_hidden(B_8,D_10)
      | ~ r2_hidden(A_7,C_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_109,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_36,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_207,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_109,c_36])).

tff(c_208,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_207])).

tff(c_211,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_208])).

tff(c_215,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_138,c_144,c_211])).

tff(c_217,plain,(
    r2_hidden('#skF_5','#skF_7') ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_216,plain,
    ( '#skF_6' != '#skF_8'
    | '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_32])).

tff(c_218,plain,(
    '#skF_6' != '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_216])).

tff(c_255,plain,(
    r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_273,plain,(
    ! [B_90,D_91,A_92,C_93] :
      ( r2_hidden(B_90,D_91)
      | ~ r2_hidden(k4_tarski(A_92,B_90),k2_zfmisc_1(C_93,D_91)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_282,plain,(
    r2_hidden('#skF_6',k1_tarski('#skF_8')) ),
    inference(resolution,[status(thm)],[c_255,c_273])).

tff(c_233,plain,(
    ! [A_79,B_80] :
      ( k4_xboole_0(k1_tarski(A_79),k1_tarski(B_80)) = k1_tarski(A_79)
      | B_80 = A_79 ) ),
    inference(cnfTransformation,[status(thm)],[f_42])).

tff(c_26,plain,(
    ! [C_19,B_18] : ~ r2_hidden(C_19,k4_xboole_0(B_18,k1_tarski(C_19))) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_246,plain,(
    ! [B_80,A_79] :
      ( ~ r2_hidden(B_80,k1_tarski(A_79))
      | B_80 = A_79 ) ),
    inference(superposition,[status(thm),theory(equality)],[c_233,c_26])).

tff(c_299,plain,(
    '#skF_6' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_282,c_246])).

tff(c_303,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_218,c_299])).

tff(c_305,plain,(
    ~ r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_310,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(negUnitSimplification,[status(thm)],[c_305,c_40])).

tff(c_312,plain,(
    ! [B_99,D_100,A_101,C_102] :
      ( r2_hidden(B_99,D_100)
      | ~ r2_hidden(k4_tarski(A_101,B_99),k2_zfmisc_1(C_102,D_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_316,plain,(
    ! [D_16] : r2_hidden(D_16,k1_tarski(D_16)) ),
    inference(resolution,[status(thm)],[c_18,c_312])).

tff(c_304,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_382,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | r2_hidden(k4_tarski('#skF_5','#skF_6'),k2_zfmisc_1('#skF_7',k1_tarski('#skF_8'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_304,c_36])).

tff(c_383,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(negUnitSimplification,[status(thm)],[c_305,c_382])).

tff(c_386,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_8,c_383])).

tff(c_390,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_316,c_386])).

tff(c_392,plain,(
    '#skF_6' = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_34,plain,
    ( r2_hidden('#skF_1','#skF_3')
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_403,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_392,c_34])).

tff(c_439,plain,(
    ! [B_136,D_137,A_138,C_139] :
      ( r2_hidden(B_136,D_137)
      | ~ r2_hidden(k4_tarski(A_138,B_136),k2_zfmisc_1(C_139,D_137)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_443,plain,(
    ! [D_16] : r2_hidden(D_16,k1_tarski(D_16)) ),
    inference(resolution,[status(thm)],[c_18,c_439])).

tff(c_485,plain,(
    ! [A_156,B_157,C_158,D_159] :
      ( r2_hidden(k4_tarski(A_156,B_157),k2_zfmisc_1(C_158,D_159))
      | ~ r2_hidden(B_157,D_159)
      | ~ r2_hidden(A_156,C_158) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_391,plain,(
    '#skF_2' = '#skF_4' ),
    inference(splitRight,[status(thm)],[c_216])).

tff(c_30,plain,
    ( ~ r2_hidden(k4_tarski('#skF_1','#skF_2'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4')))
    | '#skF_6' != '#skF_8'
    | ~ r2_hidden('#skF_5','#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_484,plain,(
    ~ r2_hidden(k4_tarski('#skF_1','#skF_4'),k2_zfmisc_1('#skF_3',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_217,c_392,c_391,c_30])).

tff(c_488,plain,
    ( ~ r2_hidden('#skF_4',k1_tarski('#skF_4'))
    | ~ r2_hidden('#skF_1','#skF_3') ),
    inference(resolution,[status(thm)],[c_485,c_484])).

tff(c_506,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_403,c_443,c_488])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n025.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 18:05:50 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.28  
% 2.19/1.28  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.28  %$ r2_hidden > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k4_tarski > k2_zfmisc_1 > k2_tarski > #nlpp > k1_tarski > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_8 > #skF_4
% 2.19/1.28  
% 2.19/1.28  %Foreground sorts:
% 2.19/1.28  
% 2.19/1.28  
% 2.19/1.28  %Background operators:
% 2.19/1.28  
% 2.19/1.28  
% 2.19/1.28  %Foreground operators:
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.28  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.19/1.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.28  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.19/1.28  tff('#skF_7', type, '#skF_7': $i).
% 2.19/1.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.19/1.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.28  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.28  tff('#skF_6', type, '#skF_6': $i).
% 2.19/1.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.28  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.28  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.28  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.28  tff('#skF_8', type, '#skF_8': $i).
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.28  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.19/1.28  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.28  
% 2.19/1.29  tff(f_62, negated_conjecture, ~(![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, k1_tarski(D))) <=> (r2_hidden(A, C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t129_zfmisc_1)).
% 2.19/1.29  tff(f_37, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 2.19/1.29  tff(f_48, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(k1_tarski(C), k1_tarski(D))) <=> ((A = C) & (B = D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t34_zfmisc_1)).
% 2.19/1.29  tff(f_42, axiom, (![A, B]: ((k4_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) <=> ~(A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t20_zfmisc_1)).
% 2.19/1.29  tff(f_55, axiom, (![A, B, C]: (r2_hidden(A, k4_xboole_0(B, k1_tarski(C))) <=> (r2_hidden(A, B) & ~(A = C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t64_zfmisc_1)).
% 2.19/1.29  tff(c_32, plain, ('#skF_2'='#skF_4' | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.19/1.29  tff(c_60, plain, (~r2_hidden('#skF_5', '#skF_7')), inference(splitLeft, [status(thm)], [c_32])).
% 2.19/1.29  tff(c_38, plain, ('#skF_2'='#skF_4' | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.19/1.29  tff(c_72, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_38])).
% 2.19/1.29  tff(c_97, plain, (![A_38, C_39, B_40, D_41]: (r2_hidden(A_38, C_39) | ~r2_hidden(k4_tarski(A_38, B_40), k2_zfmisc_1(C_39, D_41)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.29  tff(c_103, plain, (r2_hidden('#skF_5', '#skF_7')), inference(resolution, [status(thm)], [c_72, c_97])).
% 2.19/1.29  tff(c_108, plain, $false, inference(negUnitSimplification, [status(thm)], [c_60, c_103])).
% 2.19/1.29  tff(c_110, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_38])).
% 2.19/1.29  tff(c_40, plain, (r2_hidden('#skF_1', '#skF_3') | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.19/1.29  tff(c_138, plain, (r2_hidden('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_110, c_40])).
% 2.19/1.29  tff(c_18, plain, (![C_15, D_16]: (r2_hidden(k4_tarski(C_15, D_16), k2_zfmisc_1(k1_tarski(C_15), k1_tarski(D_16))))), inference(cnfTransformation, [status(thm)], [f_48])).
% 2.19/1.29  tff(c_140, plain, (![A_48, C_49, B_50, D_51]: (r2_hidden(A_48, C_49) | ~r2_hidden(k4_tarski(A_48, B_50), k2_zfmisc_1(C_49, D_51)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.29  tff(c_144, plain, (![C_15]: (r2_hidden(C_15, k1_tarski(C_15)))), inference(resolution, [status(thm)], [c_18, c_140])).
% 2.19/1.29  tff(c_8, plain, (![A_7, B_8, C_9, D_10]: (r2_hidden(k4_tarski(A_7, B_8), k2_zfmisc_1(C_9, D_10)) | ~r2_hidden(B_8, D_10) | ~r2_hidden(A_7, C_9))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.29  tff(c_109, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_38])).
% 2.19/1.29  tff(c_36, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.19/1.29  tff(c_207, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_109, c_36])).
% 2.19/1.29  tff(c_208, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_110, c_207])).
% 2.19/1.29  tff(c_211, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_8, c_208])).
% 2.19/1.29  tff(c_215, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_138, c_144, c_211])).
% 2.19/1.29  tff(c_217, plain, (r2_hidden('#skF_5', '#skF_7')), inference(splitRight, [status(thm)], [c_32])).
% 2.19/1.29  tff(c_216, plain, ('#skF_6'!='#skF_8' | '#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_32])).
% 2.19/1.29  tff(c_218, plain, ('#skF_6'!='#skF_8'), inference(splitLeft, [status(thm)], [c_216])).
% 2.19/1.29  tff(c_255, plain, (r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitLeft, [status(thm)], [c_38])).
% 2.19/1.29  tff(c_273, plain, (![B_90, D_91, A_92, C_93]: (r2_hidden(B_90, D_91) | ~r2_hidden(k4_tarski(A_92, B_90), k2_zfmisc_1(C_93, D_91)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.29  tff(c_282, plain, (r2_hidden('#skF_6', k1_tarski('#skF_8'))), inference(resolution, [status(thm)], [c_255, c_273])).
% 2.19/1.29  tff(c_233, plain, (![A_79, B_80]: (k4_xboole_0(k1_tarski(A_79), k1_tarski(B_80))=k1_tarski(A_79) | B_80=A_79)), inference(cnfTransformation, [status(thm)], [f_42])).
% 2.19/1.29  tff(c_26, plain, (![C_19, B_18]: (~r2_hidden(C_19, k4_xboole_0(B_18, k1_tarski(C_19))))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.19/1.29  tff(c_246, plain, (![B_80, A_79]: (~r2_hidden(B_80, k1_tarski(A_79)) | B_80=A_79)), inference(superposition, [status(thm), theory('equality')], [c_233, c_26])).
% 2.19/1.29  tff(c_299, plain, ('#skF_6'='#skF_8'), inference(resolution, [status(thm)], [c_282, c_246])).
% 2.19/1.29  tff(c_303, plain, $false, inference(negUnitSimplification, [status(thm)], [c_218, c_299])).
% 2.19/1.29  tff(c_305, plain, (~r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(splitRight, [status(thm)], [c_38])).
% 2.19/1.29  tff(c_310, plain, (r2_hidden('#skF_1', '#skF_3')), inference(negUnitSimplification, [status(thm)], [c_305, c_40])).
% 2.19/1.29  tff(c_312, plain, (![B_99, D_100, A_101, C_102]: (r2_hidden(B_99, D_100) | ~r2_hidden(k4_tarski(A_101, B_99), k2_zfmisc_1(C_102, D_100)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.29  tff(c_316, plain, (![D_16]: (r2_hidden(D_16, k1_tarski(D_16)))), inference(resolution, [status(thm)], [c_18, c_312])).
% 2.19/1.29  tff(c_304, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_38])).
% 2.19/1.29  tff(c_382, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | r2_hidden(k4_tarski('#skF_5', '#skF_6'), k2_zfmisc_1('#skF_7', k1_tarski('#skF_8')))), inference(demodulation, [status(thm), theory('equality')], [c_304, c_36])).
% 2.19/1.29  tff(c_383, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(negUnitSimplification, [status(thm)], [c_305, c_382])).
% 2.19/1.29  tff(c_386, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_8, c_383])).
% 2.19/1.29  tff(c_390, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_310, c_316, c_386])).
% 2.19/1.29  tff(c_392, plain, ('#skF_6'='#skF_8'), inference(splitRight, [status(thm)], [c_216])).
% 2.19/1.29  tff(c_34, plain, (r2_hidden('#skF_1', '#skF_3') | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.19/1.29  tff(c_403, plain, (r2_hidden('#skF_1', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_217, c_392, c_34])).
% 2.19/1.29  tff(c_439, plain, (![B_136, D_137, A_138, C_139]: (r2_hidden(B_136, D_137) | ~r2_hidden(k4_tarski(A_138, B_136), k2_zfmisc_1(C_139, D_137)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.29  tff(c_443, plain, (![D_16]: (r2_hidden(D_16, k1_tarski(D_16)))), inference(resolution, [status(thm)], [c_18, c_439])).
% 2.19/1.29  tff(c_485, plain, (![A_156, B_157, C_158, D_159]: (r2_hidden(k4_tarski(A_156, B_157), k2_zfmisc_1(C_158, D_159)) | ~r2_hidden(B_157, D_159) | ~r2_hidden(A_156, C_158))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.19/1.29  tff(c_391, plain, ('#skF_2'='#skF_4'), inference(splitRight, [status(thm)], [c_216])).
% 2.19/1.29  tff(c_30, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_2'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4'))) | '#skF_6'!='#skF_8' | ~r2_hidden('#skF_5', '#skF_7')), inference(cnfTransformation, [status(thm)], [f_62])).
% 2.19/1.29  tff(c_484, plain, (~r2_hidden(k4_tarski('#skF_1', '#skF_4'), k2_zfmisc_1('#skF_3', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_217, c_392, c_391, c_30])).
% 2.19/1.29  tff(c_488, plain, (~r2_hidden('#skF_4', k1_tarski('#skF_4')) | ~r2_hidden('#skF_1', '#skF_3')), inference(resolution, [status(thm)], [c_485, c_484])).
% 2.19/1.29  tff(c_506, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_403, c_443, c_488])).
% 2.19/1.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.29  
% 2.19/1.29  Inference rules
% 2.19/1.29  ----------------------
% 2.19/1.29  #Ref     : 0
% 2.19/1.29  #Sup     : 90
% 2.19/1.29  #Fact    : 0
% 2.19/1.29  #Define  : 0
% 2.19/1.29  #Split   : 4
% 2.19/1.29  #Chain   : 0
% 2.19/1.29  #Close   : 0
% 2.19/1.29  
% 2.19/1.29  Ordering : KBO
% 2.19/1.29  
% 2.19/1.29  Simplification rules
% 2.19/1.29  ----------------------
% 2.19/1.29  #Subsume      : 9
% 2.19/1.29  #Demod        : 27
% 2.19/1.29  #Tautology    : 67
% 2.19/1.29  #SimpNegUnit  : 6
% 2.19/1.29  #BackRed      : 0
% 2.19/1.29  
% 2.19/1.29  #Partial instantiations: 0
% 2.19/1.29  #Strategies tried      : 1
% 2.19/1.29  
% 2.19/1.29  Timing (in seconds)
% 2.19/1.29  ----------------------
% 2.19/1.30  Preprocessing        : 0.29
% 2.19/1.30  Parsing              : 0.15
% 2.19/1.30  CNF conversion       : 0.02
% 2.19/1.30  Main loop            : 0.24
% 2.19/1.30  Inferencing          : 0.10
% 2.19/1.30  Reduction            : 0.07
% 2.19/1.30  Demodulation         : 0.04
% 2.19/1.30  BG Simplification    : 0.01
% 2.19/1.30  Subsumption          : 0.04
% 2.19/1.30  Abstraction          : 0.01
% 2.19/1.30  MUC search           : 0.00
% 2.19/1.30  Cooper               : 0.00
% 2.19/1.30  Total                : 0.57
% 2.19/1.30  Index Insertion      : 0.00
% 2.19/1.30  Index Deletion       : 0.00
% 2.19/1.30  Index Matching       : 0.00
% 2.19/1.30  BG Taut test         : 0.00
%------------------------------------------------------------------------------

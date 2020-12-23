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
% DateTime   : Thu Dec  3 09:54:27 EST 2020

% Result     : Theorem 2.98s
% Output     : CNFRefutation 3.11s
% Verified   : 
% Statistics : Number of formulae       :   58 ( 168 expanded)
%              Number of leaves         :   19 (  64 expanded)
%              Depth                    :    8
%              Number of atoms          :   84 ( 376 expanded)
%              Number of equality atoms :   15 (  46 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_tarski,type,(
    k4_tarski: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( r1_tarski(k2_zfmisc_1(A,B),k2_zfmisc_1(C,D))
       => ( k2_zfmisc_1(A,B) = k1_xboole_0
          | ( r1_tarski(A,C)
            & r1_tarski(B,D) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t138_zfmisc_1)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_46,axiom,(
    ! [A,B,C,D] :
      ( r2_hidden(k4_tarski(A,B),k2_zfmisc_1(C,D))
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,D) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l54_zfmisc_1)).

tff(f_52,axiom,(
    ! [A,B] :
      ( k2_zfmisc_1(A,B) = k1_xboole_0
    <=> ( A = k1_xboole_0
        | B = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t113_zfmisc_1)).

tff(c_22,plain,
    ( ~ r1_tarski('#skF_4','#skF_6')
    | ~ r1_tarski('#skF_3','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_50,plain,(
    ~ r1_tarski('#skF_3','#skF_5') ),
    inference(splitLeft,[status(thm)],[c_22])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_26,plain,(
    r1_tarski(k2_zfmisc_1('#skF_3','#skF_4'),k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_98,plain,(
    ! [A_45,B_46,C_47,D_48] :
      ( r2_hidden(k4_tarski(A_45,B_46),k2_zfmisc_1(C_47,D_48))
      | ~ r2_hidden(B_46,D_48)
      | ~ r2_hidden(A_45,C_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_2,plain,(
    ! [C_5,B_2,A_1] :
      ( r2_hidden(C_5,B_2)
      | ~ r2_hidden(C_5,A_1)
      | ~ r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_347,plain,(
    ! [B_221,D_223,C_224,B_225,A_222] :
      ( r2_hidden(k4_tarski(A_222,B_221),B_225)
      | ~ r1_tarski(k2_zfmisc_1(C_224,D_223),B_225)
      | ~ r2_hidden(B_221,D_223)
      | ~ r2_hidden(A_222,C_224) ) ),
    inference(resolution,[status(thm)],[c_98,c_2])).

tff(c_364,plain,(
    ! [A_226,B_227] :
      ( r2_hidden(k4_tarski(A_226,B_227),k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(B_227,'#skF_4')
      | ~ r2_hidden(A_226,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_347])).

tff(c_14,plain,(
    ! [A_8,C_10,B_9,D_11] :
      ( r2_hidden(A_8,C_10)
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_373,plain,(
    ! [A_226,B_227] :
      ( r2_hidden(A_226,'#skF_5')
      | ~ r2_hidden(B_227,'#skF_4')
      | ~ r2_hidden(A_226,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_364,c_14])).

tff(c_377,plain,(
    ! [B_228] : ~ r2_hidden(B_228,'#skF_4') ),
    inference(splitLeft,[status(thm)],[c_373])).

tff(c_397,plain,(
    k1_xboole_0 = '#skF_4' ),
    inference(resolution,[status(thm)],[c_8,c_377])).

tff(c_18,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_405,plain,(
    ! [A_12] : k2_zfmisc_1(A_12,'#skF_4') = '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_397,c_18])).

tff(c_24,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_407,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != '#skF_4' ),
    inference(demodulation,[status(thm),theory(equality)],[c_397,c_24])).

tff(c_450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_405,c_407])).

tff(c_452,plain,(
    ! [A_234] :
      ( r2_hidden(A_234,'#skF_5')
      | ~ r2_hidden(A_234,'#skF_3') ) ),
    inference(splitRight,[status(thm)],[c_373])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_510,plain,(
    ! [A_237] :
      ( r1_tarski(A_237,'#skF_5')
      | ~ r2_hidden('#skF_1'(A_237,'#skF_5'),'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_452,c_4])).

tff(c_518,plain,(
    r1_tarski('#skF_3','#skF_5') ),
    inference(resolution,[status(thm)],[c_6,c_510])).

tff(c_523,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_50,c_518])).

tff(c_524,plain,(
    ~ r1_tarski('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_22])).

tff(c_573,plain,(
    ! [A_265,B_266,C_267,D_268] :
      ( r2_hidden(k4_tarski(A_265,B_266),k2_zfmisc_1(C_267,D_268))
      | ~ r2_hidden(B_266,D_268)
      | ~ r2_hidden(A_265,C_267) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_649,plain,(
    ! [B_285,B_286,D_283,A_284,C_287] :
      ( r2_hidden(k4_tarski(A_284,B_285),B_286)
      | ~ r1_tarski(k2_zfmisc_1(C_287,D_283),B_286)
      | ~ r2_hidden(B_285,D_283)
      | ~ r2_hidden(A_284,C_287) ) ),
    inference(resolution,[status(thm)],[c_573,c_2])).

tff(c_751,plain,(
    ! [A_424,B_425] :
      ( r2_hidden(k4_tarski(A_424,B_425),k2_zfmisc_1('#skF_5','#skF_6'))
      | ~ r2_hidden(B_425,'#skF_4')
      | ~ r2_hidden(A_424,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_26,c_649])).

tff(c_12,plain,(
    ! [B_9,D_11,A_8,C_10] :
      ( r2_hidden(B_9,D_11)
      | ~ r2_hidden(k4_tarski(A_8,B_9),k2_zfmisc_1(C_10,D_11)) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_767,plain,(
    ! [B_425,A_424] :
      ( r2_hidden(B_425,'#skF_6')
      | ~ r2_hidden(B_425,'#skF_4')
      | ~ r2_hidden(A_424,'#skF_3') ) ),
    inference(resolution,[status(thm)],[c_751,c_12])).

tff(c_925,plain,(
    ! [A_440] : ~ r2_hidden(A_440,'#skF_3') ),
    inference(splitLeft,[status(thm)],[c_767])).

tff(c_945,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(resolution,[status(thm)],[c_8,c_925])).

tff(c_20,plain,(
    ! [B_13] : k2_zfmisc_1(k1_xboole_0,B_13) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_955,plain,(
    ! [B_13] : k2_zfmisc_1('#skF_3',B_13) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_945,c_945,c_20])).

tff(c_956,plain,(
    k2_zfmisc_1('#skF_3','#skF_4') != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_945,c_24])).

tff(c_967,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_955,c_956])).

tff(c_969,plain,(
    ! [B_442] :
      ( r2_hidden(B_442,'#skF_6')
      | ~ r2_hidden(B_442,'#skF_4') ) ),
    inference(splitRight,[status(thm)],[c_767])).

tff(c_978,plain,(
    ! [A_443] :
      ( r1_tarski(A_443,'#skF_6')
      | ~ r2_hidden('#skF_1'(A_443,'#skF_6'),'#skF_4') ) ),
    inference(resolution,[status(thm)],[c_969,c_4])).

tff(c_986,plain,(
    r1_tarski('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_6,c_978])).

tff(c_991,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_524,c_524,c_986])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:26:50 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.98/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.50  
% 2.98/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.98/1.51  %$ r2_hidden > r1_tarski > k4_tarski > k2_zfmisc_1 > #nlpp > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_3 > #skF_4 > #skF_1
% 2.98/1.51  
% 2.98/1.51  %Foreground sorts:
% 2.98/1.51  
% 2.98/1.51  
% 2.98/1.51  %Background operators:
% 2.98/1.51  
% 2.98/1.51  
% 2.98/1.51  %Foreground operators:
% 2.98/1.51  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.98/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.98/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.98/1.51  tff(k4_tarski, type, k4_tarski: ($i * $i) > $i).
% 2.98/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.98/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.98/1.51  tff('#skF_5', type, '#skF_5': $i).
% 2.98/1.51  tff('#skF_6', type, '#skF_6': $i).
% 2.98/1.51  tff('#skF_3', type, '#skF_3': $i).
% 2.98/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.98/1.51  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 2.98/1.51  tff('#skF_4', type, '#skF_4': $i).
% 2.98/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.98/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.98/1.51  
% 3.11/1.52  tff(f_61, negated_conjecture, ~(![A, B, C, D]: (r1_tarski(k2_zfmisc_1(A, B), k2_zfmisc_1(C, D)) => ((k2_zfmisc_1(A, B) = k1_xboole_0) | (r1_tarski(A, C) & r1_tarski(B, D))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t138_zfmisc_1)).
% 3.11/1.52  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.11/1.52  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.11/1.52  tff(f_46, axiom, (![A, B, C, D]: (r2_hidden(k4_tarski(A, B), k2_zfmisc_1(C, D)) <=> (r2_hidden(A, C) & r2_hidden(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l54_zfmisc_1)).
% 3.11/1.52  tff(f_52, axiom, (![A, B]: ((k2_zfmisc_1(A, B) = k1_xboole_0) <=> ((A = k1_xboole_0) | (B = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t113_zfmisc_1)).
% 3.11/1.52  tff(c_22, plain, (~r1_tarski('#skF_4', '#skF_6') | ~r1_tarski('#skF_3', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.11/1.52  tff(c_50, plain, (~r1_tarski('#skF_3', '#skF_5')), inference(splitLeft, [status(thm)], [c_22])).
% 3.11/1.52  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.11/1.52  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.11/1.52  tff(c_26, plain, (r1_tarski(k2_zfmisc_1('#skF_3', '#skF_4'), k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.11/1.52  tff(c_98, plain, (![A_45, B_46, C_47, D_48]: (r2_hidden(k4_tarski(A_45, B_46), k2_zfmisc_1(C_47, D_48)) | ~r2_hidden(B_46, D_48) | ~r2_hidden(A_45, C_47))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.11/1.52  tff(c_2, plain, (![C_5, B_2, A_1]: (r2_hidden(C_5, B_2) | ~r2_hidden(C_5, A_1) | ~r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.11/1.52  tff(c_347, plain, (![B_221, D_223, C_224, B_225, A_222]: (r2_hidden(k4_tarski(A_222, B_221), B_225) | ~r1_tarski(k2_zfmisc_1(C_224, D_223), B_225) | ~r2_hidden(B_221, D_223) | ~r2_hidden(A_222, C_224))), inference(resolution, [status(thm)], [c_98, c_2])).
% 3.11/1.52  tff(c_364, plain, (![A_226, B_227]: (r2_hidden(k4_tarski(A_226, B_227), k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(B_227, '#skF_4') | ~r2_hidden(A_226, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_347])).
% 3.11/1.52  tff(c_14, plain, (![A_8, C_10, B_9, D_11]: (r2_hidden(A_8, C_10) | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(C_10, D_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.11/1.52  tff(c_373, plain, (![A_226, B_227]: (r2_hidden(A_226, '#skF_5') | ~r2_hidden(B_227, '#skF_4') | ~r2_hidden(A_226, '#skF_3'))), inference(resolution, [status(thm)], [c_364, c_14])).
% 3.11/1.52  tff(c_377, plain, (![B_228]: (~r2_hidden(B_228, '#skF_4'))), inference(splitLeft, [status(thm)], [c_373])).
% 3.11/1.52  tff(c_397, plain, (k1_xboole_0='#skF_4'), inference(resolution, [status(thm)], [c_8, c_377])).
% 3.11/1.52  tff(c_18, plain, (![A_12]: (k2_zfmisc_1(A_12, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.11/1.52  tff(c_405, plain, (![A_12]: (k2_zfmisc_1(A_12, '#skF_4')='#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_397, c_397, c_18])).
% 3.11/1.52  tff(c_24, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.11/1.52  tff(c_407, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!='#skF_4'), inference(demodulation, [status(thm), theory('equality')], [c_397, c_24])).
% 3.11/1.52  tff(c_450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_405, c_407])).
% 3.11/1.52  tff(c_452, plain, (![A_234]: (r2_hidden(A_234, '#skF_5') | ~r2_hidden(A_234, '#skF_3'))), inference(splitRight, [status(thm)], [c_373])).
% 3.11/1.52  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.11/1.52  tff(c_510, plain, (![A_237]: (r1_tarski(A_237, '#skF_5') | ~r2_hidden('#skF_1'(A_237, '#skF_5'), '#skF_3'))), inference(resolution, [status(thm)], [c_452, c_4])).
% 3.11/1.52  tff(c_518, plain, (r1_tarski('#skF_3', '#skF_5')), inference(resolution, [status(thm)], [c_6, c_510])).
% 3.11/1.52  tff(c_523, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_50, c_518])).
% 3.11/1.52  tff(c_524, plain, (~r1_tarski('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_22])).
% 3.11/1.52  tff(c_573, plain, (![A_265, B_266, C_267, D_268]: (r2_hidden(k4_tarski(A_265, B_266), k2_zfmisc_1(C_267, D_268)) | ~r2_hidden(B_266, D_268) | ~r2_hidden(A_265, C_267))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.11/1.52  tff(c_649, plain, (![B_285, B_286, D_283, A_284, C_287]: (r2_hidden(k4_tarski(A_284, B_285), B_286) | ~r1_tarski(k2_zfmisc_1(C_287, D_283), B_286) | ~r2_hidden(B_285, D_283) | ~r2_hidden(A_284, C_287))), inference(resolution, [status(thm)], [c_573, c_2])).
% 3.11/1.52  tff(c_751, plain, (![A_424, B_425]: (r2_hidden(k4_tarski(A_424, B_425), k2_zfmisc_1('#skF_5', '#skF_6')) | ~r2_hidden(B_425, '#skF_4') | ~r2_hidden(A_424, '#skF_3'))), inference(resolution, [status(thm)], [c_26, c_649])).
% 3.11/1.52  tff(c_12, plain, (![B_9, D_11, A_8, C_10]: (r2_hidden(B_9, D_11) | ~r2_hidden(k4_tarski(A_8, B_9), k2_zfmisc_1(C_10, D_11)))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.11/1.52  tff(c_767, plain, (![B_425, A_424]: (r2_hidden(B_425, '#skF_6') | ~r2_hidden(B_425, '#skF_4') | ~r2_hidden(A_424, '#skF_3'))), inference(resolution, [status(thm)], [c_751, c_12])).
% 3.11/1.52  tff(c_925, plain, (![A_440]: (~r2_hidden(A_440, '#skF_3'))), inference(splitLeft, [status(thm)], [c_767])).
% 3.11/1.52  tff(c_945, plain, (k1_xboole_0='#skF_3'), inference(resolution, [status(thm)], [c_8, c_925])).
% 3.11/1.52  tff(c_20, plain, (![B_13]: (k2_zfmisc_1(k1_xboole_0, B_13)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_52])).
% 3.11/1.52  tff(c_955, plain, (![B_13]: (k2_zfmisc_1('#skF_3', B_13)='#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_945, c_945, c_20])).
% 3.11/1.52  tff(c_956, plain, (k2_zfmisc_1('#skF_3', '#skF_4')!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_945, c_24])).
% 3.11/1.52  tff(c_967, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_955, c_956])).
% 3.11/1.52  tff(c_969, plain, (![B_442]: (r2_hidden(B_442, '#skF_6') | ~r2_hidden(B_442, '#skF_4'))), inference(splitRight, [status(thm)], [c_767])).
% 3.11/1.52  tff(c_978, plain, (![A_443]: (r1_tarski(A_443, '#skF_6') | ~r2_hidden('#skF_1'(A_443, '#skF_6'), '#skF_4'))), inference(resolution, [status(thm)], [c_969, c_4])).
% 3.11/1.52  tff(c_986, plain, (r1_tarski('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_6, c_978])).
% 3.11/1.52  tff(c_991, plain, $false, inference(negUnitSimplification, [status(thm)], [c_524, c_524, c_986])).
% 3.11/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.11/1.52  
% 3.11/1.52  Inference rules
% 3.11/1.52  ----------------------
% 3.11/1.52  #Ref     : 0
% 3.11/1.52  #Sup     : 229
% 3.11/1.52  #Fact    : 0
% 3.11/1.52  #Define  : 0
% 3.11/1.52  #Split   : 9
% 3.11/1.52  #Chain   : 0
% 3.11/1.52  #Close   : 0
% 3.11/1.52  
% 3.11/1.52  Ordering : KBO
% 3.11/1.52  
% 3.11/1.52  Simplification rules
% 3.11/1.52  ----------------------
% 3.11/1.52  #Subsume      : 64
% 3.11/1.52  #Demod        : 84
% 3.11/1.52  #Tautology    : 47
% 3.11/1.52  #SimpNegUnit  : 12
% 3.11/1.52  #BackRed      : 46
% 3.11/1.52  
% 3.11/1.52  #Partial instantiations: 148
% 3.11/1.52  #Strategies tried      : 1
% 3.11/1.52  
% 3.11/1.52  Timing (in seconds)
% 3.11/1.52  ----------------------
% 3.11/1.52  Preprocessing        : 0.30
% 3.11/1.52  Parsing              : 0.16
% 3.11/1.52  CNF conversion       : 0.02
% 3.11/1.52  Main loop            : 0.41
% 3.11/1.52  Inferencing          : 0.17
% 3.11/1.52  Reduction            : 0.10
% 3.11/1.52  Demodulation         : 0.07
% 3.11/1.52  BG Simplification    : 0.02
% 3.11/1.52  Subsumption          : 0.09
% 3.11/1.52  Abstraction          : 0.02
% 3.11/1.52  MUC search           : 0.00
% 3.11/1.52  Cooper               : 0.00
% 3.11/1.52  Total                : 0.74
% 3.11/1.52  Index Insertion      : 0.00
% 3.11/1.52  Index Deletion       : 0.00
% 3.11/1.52  Index Matching       : 0.00
% 3.11/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------

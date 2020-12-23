%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:43 EST 2020

% Result     : Theorem 2.68s
% Output     : CNFRefutation 2.68s
% Verified   : 
% Statistics : Number of formulae       :   58 (  77 expanded)
%              Number of leaves         :   24 (  36 expanded)
%              Depth                    :    7
%              Number of atoms          :   60 (  94 expanded)
%              Number of equality atoms :   14 (  25 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_61,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(A,k1_tarski(B)) = A
      <=> ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_39,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_26,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_41,plain,(
    ~ r2_hidden('#skF_2','#skF_1') ),
    inference(splitLeft,[status(thm)],[c_26])).

tff(c_100,plain,(
    ! [A_39,B_40] :
      ( r1_xboole_0(k1_tarski(A_39),B_40)
      | r2_hidden(A_39,B_40) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_2,plain,(
    ! [B_2,A_1] :
      ( r1_xboole_0(B_2,A_1)
      | ~ r1_xboole_0(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_116,plain,(
    ! [B_43,A_44] :
      ( r1_xboole_0(B_43,k1_tarski(A_44))
      | r2_hidden(A_44,B_43) ) ),
    inference(resolution,[status(thm)],[c_100,c_2])).

tff(c_8,plain,(
    ! [A_7,B_8] :
      ( k4_xboole_0(A_7,B_8) = A_7
      | ~ r1_xboole_0(A_7,B_8) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_253,plain,(
    ! [B_66,A_67] :
      ( k4_xboole_0(B_66,k1_tarski(A_67)) = B_66
      | r2_hidden(A_67,B_66) ) ),
    inference(resolution,[status(thm)],[c_116,c_8])).

tff(c_24,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | r2_hidden('#skF_4','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_124,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1' ),
    inference(splitLeft,[status(thm)],[c_24])).

tff(c_274,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_253,c_124])).

tff(c_300,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_41,c_274])).

tff(c_301,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_302,plain,(
    k4_xboole_0('#skF_1',k1_tarski('#skF_2')) = '#skF_1' ),
    inference(splitRight,[status(thm)],[c_24])).

tff(c_28,plain,
    ( k4_xboole_0('#skF_1',k1_tarski('#skF_2')) != '#skF_1'
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_317,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_302,c_28])).

tff(c_6,plain,(
    ! [A_5,B_6] : r1_xboole_0(k4_xboole_0(A_5,B_6),B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_327,plain,(
    r1_xboole_0('#skF_3',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_6])).

tff(c_346,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),'#skF_3') ),
    inference(resolution,[status(thm)],[c_327,c_2])).

tff(c_12,plain,(
    ! [A_9] : k2_tarski(A_9,A_9) = k1_tarski(A_9) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_364,plain,(
    ! [A_68,C_69,B_70] :
      ( ~ r2_hidden(A_68,C_69)
      | ~ r1_xboole_0(k2_tarski(A_68,B_70),C_69) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_423,plain,(
    ! [A_71,C_72] :
      ( ~ r2_hidden(A_71,C_72)
      | ~ r1_xboole_0(k1_tarski(A_71),C_72) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_364])).

tff(c_426,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_346,c_423])).

tff(c_452,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_301,c_426])).

tff(c_453,plain,(
    r2_hidden('#skF_4','#skF_3') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_454,plain,(
    r2_hidden('#skF_2','#skF_1') ),
    inference(splitRight,[status(thm)],[c_26])).

tff(c_30,plain,
    ( ~ r2_hidden('#skF_2','#skF_1')
    | k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_506,plain,(
    k4_xboole_0('#skF_3',k1_tarski('#skF_4')) = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_454,c_30])).

tff(c_455,plain,(
    ! [B_73,A_74] :
      ( r1_xboole_0(B_73,A_74)
      | ~ r1_xboole_0(A_74,B_73) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_458,plain,(
    ! [B_6,A_5] : r1_xboole_0(B_6,k4_xboole_0(A_5,B_6)) ),
    inference(resolution,[status(thm)],[c_6,c_455])).

tff(c_513,plain,(
    r1_xboole_0(k1_tarski('#skF_4'),'#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_506,c_458])).

tff(c_587,plain,(
    ! [A_91,C_92,B_93] :
      ( ~ r2_hidden(A_91,C_92)
      | ~ r1_xboole_0(k2_tarski(A_91,B_93),C_92) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_611,plain,(
    ! [A_94,C_95] :
      ( ~ r2_hidden(A_94,C_95)
      | ~ r1_xboole_0(k1_tarski(A_94),C_95) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_587])).

tff(c_629,plain,(
    ~ r2_hidden('#skF_4','#skF_3') ),
    inference(resolution,[status(thm)],[c_513,c_611])).

tff(c_641,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_453,c_629])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:51:41 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.20/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.68/1.72  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.73  
% 2.68/1.73  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.74  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.68/1.74  
% 2.68/1.74  %Foreground sorts:
% 2.68/1.74  
% 2.68/1.74  
% 2.68/1.74  %Background operators:
% 2.68/1.74  
% 2.68/1.74  
% 2.68/1.74  %Foreground operators:
% 2.68/1.74  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.68/1.74  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.68/1.74  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.68/1.74  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.68/1.74  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.68/1.74  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.68/1.74  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.68/1.74  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.68/1.74  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.68/1.74  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.68/1.74  tff('#skF_2', type, '#skF_2': $i).
% 2.68/1.74  tff('#skF_3', type, '#skF_3': $i).
% 2.68/1.74  tff('#skF_1', type, '#skF_1': $i).
% 2.68/1.74  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.68/1.74  tff('#skF_4', type, '#skF_4': $i).
% 2.68/1.74  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.68/1.74  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.68/1.74  
% 2.68/1.76  tff(f_61, negated_conjecture, ~(![A, B]: ((k4_xboole_0(A, k1_tarski(B)) = A) <=> ~r2_hidden(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_zfmisc_1)).
% 2.68/1.76  tff(f_50, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 2.68/1.76  tff(f_29, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 2.68/1.76  tff(f_37, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.68/1.76  tff(f_33, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.68/1.76  tff(f_39, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 2.68/1.76  tff(f_55, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.68/1.76  tff(c_26, plain, (~r2_hidden('#skF_2', '#skF_1') | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.68/1.76  tff(c_41, plain, (~r2_hidden('#skF_2', '#skF_1')), inference(splitLeft, [status(thm)], [c_26])).
% 2.68/1.76  tff(c_100, plain, (![A_39, B_40]: (r1_xboole_0(k1_tarski(A_39), B_40) | r2_hidden(A_39, B_40))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.68/1.76  tff(c_2, plain, (![B_2, A_1]: (r1_xboole_0(B_2, A_1) | ~r1_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.68/1.76  tff(c_116, plain, (![B_43, A_44]: (r1_xboole_0(B_43, k1_tarski(A_44)) | r2_hidden(A_44, B_43))), inference(resolution, [status(thm)], [c_100, c_2])).
% 2.68/1.76  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, B_8)=A_7 | ~r1_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_37])).
% 2.68/1.76  tff(c_253, plain, (![B_66, A_67]: (k4_xboole_0(B_66, k1_tarski(A_67))=B_66 | r2_hidden(A_67, B_66))), inference(resolution, [status(thm)], [c_116, c_8])).
% 2.68/1.76  tff(c_24, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | r2_hidden('#skF_4', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.68/1.76  tff(c_124, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1'), inference(splitLeft, [status(thm)], [c_24])).
% 2.68/1.76  tff(c_274, plain, (r2_hidden('#skF_2', '#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_253, c_124])).
% 2.68/1.76  tff(c_300, plain, $false, inference(negUnitSimplification, [status(thm)], [c_41, c_274])).
% 2.68/1.76  tff(c_301, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_24])).
% 2.68/1.76  tff(c_302, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))='#skF_1'), inference(splitRight, [status(thm)], [c_24])).
% 2.68/1.76  tff(c_28, plain, (k4_xboole_0('#skF_1', k1_tarski('#skF_2'))!='#skF_1' | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.68/1.76  tff(c_317, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_302, c_28])).
% 2.68/1.76  tff(c_6, plain, (![A_5, B_6]: (r1_xboole_0(k4_xboole_0(A_5, B_6), B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.68/1.76  tff(c_327, plain, (r1_xboole_0('#skF_3', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_317, c_6])).
% 2.68/1.76  tff(c_346, plain, (r1_xboole_0(k1_tarski('#skF_4'), '#skF_3')), inference(resolution, [status(thm)], [c_327, c_2])).
% 2.68/1.76  tff(c_12, plain, (![A_9]: (k2_tarski(A_9, A_9)=k1_tarski(A_9))), inference(cnfTransformation, [status(thm)], [f_39])).
% 2.68/1.76  tff(c_364, plain, (![A_68, C_69, B_70]: (~r2_hidden(A_68, C_69) | ~r1_xboole_0(k2_tarski(A_68, B_70), C_69))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.68/1.76  tff(c_423, plain, (![A_71, C_72]: (~r2_hidden(A_71, C_72) | ~r1_xboole_0(k1_tarski(A_71), C_72))), inference(superposition, [status(thm), theory('equality')], [c_12, c_364])).
% 2.68/1.76  tff(c_426, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_346, c_423])).
% 2.68/1.76  tff(c_452, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_301, c_426])).
% 2.68/1.76  tff(c_453, plain, (r2_hidden('#skF_4', '#skF_3')), inference(splitRight, [status(thm)], [c_26])).
% 2.68/1.76  tff(c_454, plain, (r2_hidden('#skF_2', '#skF_1')), inference(splitRight, [status(thm)], [c_26])).
% 2.68/1.76  tff(c_30, plain, (~r2_hidden('#skF_2', '#skF_1') | k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.68/1.76  tff(c_506, plain, (k4_xboole_0('#skF_3', k1_tarski('#skF_4'))='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_454, c_30])).
% 2.68/1.76  tff(c_455, plain, (![B_73, A_74]: (r1_xboole_0(B_73, A_74) | ~r1_xboole_0(A_74, B_73))), inference(cnfTransformation, [status(thm)], [f_29])).
% 2.68/1.76  tff(c_458, plain, (![B_6, A_5]: (r1_xboole_0(B_6, k4_xboole_0(A_5, B_6)))), inference(resolution, [status(thm)], [c_6, c_455])).
% 2.68/1.76  tff(c_513, plain, (r1_xboole_0(k1_tarski('#skF_4'), '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_506, c_458])).
% 2.68/1.76  tff(c_587, plain, (![A_91, C_92, B_93]: (~r2_hidden(A_91, C_92) | ~r1_xboole_0(k2_tarski(A_91, B_93), C_92))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.68/1.76  tff(c_611, plain, (![A_94, C_95]: (~r2_hidden(A_94, C_95) | ~r1_xboole_0(k1_tarski(A_94), C_95))), inference(superposition, [status(thm), theory('equality')], [c_12, c_587])).
% 2.68/1.76  tff(c_629, plain, (~r2_hidden('#skF_4', '#skF_3')), inference(resolution, [status(thm)], [c_513, c_611])).
% 2.68/1.76  tff(c_641, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_453, c_629])).
% 2.68/1.76  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.68/1.76  
% 2.68/1.76  Inference rules
% 2.68/1.76  ----------------------
% 2.68/1.76  #Ref     : 0
% 2.68/1.76  #Sup     : 147
% 2.68/1.76  #Fact    : 0
% 2.68/1.76  #Define  : 0
% 2.68/1.76  #Split   : 2
% 2.68/1.76  #Chain   : 0
% 2.68/1.76  #Close   : 0
% 2.68/1.76  
% 2.68/1.76  Ordering : KBO
% 2.68/1.76  
% 2.68/1.76  Simplification rules
% 2.68/1.76  ----------------------
% 2.68/1.76  #Subsume      : 10
% 2.68/1.76  #Demod        : 43
% 2.68/1.76  #Tautology    : 73
% 2.68/1.76  #SimpNegUnit  : 2
% 2.68/1.76  #BackRed      : 0
% 2.68/1.76  
% 2.68/1.76  #Partial instantiations: 0
% 2.68/1.76  #Strategies tried      : 1
% 2.68/1.76  
% 2.68/1.76  Timing (in seconds)
% 2.68/1.76  ----------------------
% 2.68/1.76  Preprocessing        : 0.47
% 2.68/1.76  Parsing              : 0.25
% 2.68/1.76  CNF conversion       : 0.03
% 2.68/1.76  Main loop            : 0.41
% 2.68/1.76  Inferencing          : 0.17
% 2.68/1.76  Reduction            : 0.11
% 2.68/1.76  Demodulation         : 0.08
% 2.68/1.76  BG Simplification    : 0.02
% 2.68/1.76  Subsumption          : 0.06
% 2.68/1.77  Abstraction          : 0.03
% 2.68/1.77  MUC search           : 0.00
% 2.68/1.77  Cooper               : 0.00
% 2.68/1.77  Total                : 0.93
% 2.68/1.77  Index Insertion      : 0.00
% 2.68/1.77  Index Deletion       : 0.00
% 2.68/1.77  Index Matching       : 0.00
% 2.68/1.77  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n024.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:14 EST 2020

% Result     : Theorem 2.19s
% Output     : CNFRefutation 2.19s
% Verified   : 
% Statistics : Number of formulae       :   77 ( 143 expanded)
%              Number of leaves         :   20 (  53 expanded)
%              Depth                    :    6
%              Number of atoms          :   95 ( 244 expanded)
%              Number of equality atoms :   24 (  62 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff(f_33,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_59,negated_conjecture,(
    ~ ! [A,B,C] :
        ( k4_xboole_0(k2_tarski(A,B),C) = k2_tarski(A,B)
      <=> ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_zfmisc_1)).

tff(f_50,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,B)
        & ~ r2_hidden(C,B)
        & ~ r1_xboole_0(k2_tarski(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t57_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_40,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(c_8,plain,(
    ! [B_6,A_5] : k2_tarski(B_6,A_5) = k2_tarski(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_20,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_126,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_20])).

tff(c_18,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_125,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(splitLeft,[status(thm)],[c_18])).

tff(c_127,plain,(
    ! [A_33,C_34,B_35] :
      ( r1_xboole_0(k2_tarski(A_33,C_34),B_35)
      | r2_hidden(C_34,B_35)
      | r2_hidden(A_33,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k4_xboole_0(A_3,B_4) = A_3
      | ~ r1_xboole_0(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_175,plain,(
    ! [A_48,C_49,B_50] :
      ( k4_xboole_0(k2_tarski(A_48,C_49),B_50) = k2_tarski(A_48,C_49)
      | r2_hidden(C_49,B_50)
      | r2_hidden(A_48,B_50) ) ),
    inference(resolution,[status(thm)],[c_127,c_4])).

tff(c_16,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2')
    | r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_167,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2') ),
    inference(splitLeft,[status(thm)],[c_16])).

tff(c_184,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_175,c_167])).

tff(c_213,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_126,c_125,c_184])).

tff(c_214,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_216,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_214])).

tff(c_215,plain,(
    k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') = k2_tarski('#skF_1','#skF_2') ),
    inference(splitRight,[status(thm)],[c_16])).

tff(c_22,plain,
    ( k4_xboole_0(k2_tarski('#skF_1','#skF_2'),'#skF_3') != k2_tarski('#skF_1','#skF_2')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_255,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_22])).

tff(c_6,plain,(
    ! [A_3,B_4] :
      ( r1_xboole_0(A_3,B_4)
      | k4_xboole_0(A_3,B_4) != A_3 ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_80,plain,(
    ! [A_25,C_26,B_27] :
      ( ~ r2_hidden(A_25,C_26)
      | ~ r1_xboole_0(k2_tarski(A_25,B_27),C_26) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_146,plain,(
    ! [A_36,B_37,B_38] :
      ( ~ r2_hidden(A_36,B_37)
      | k4_xboole_0(k2_tarski(A_36,B_38),B_37) != k2_tarski(A_36,B_38) ) ),
    inference(resolution,[status(thm)],[c_6,c_80])).

tff(c_149,plain,(
    ! [A_5,B_37,B_6] :
      ( ~ r2_hidden(A_5,B_37)
      | k4_xboole_0(k2_tarski(B_6,A_5),B_37) != k2_tarski(A_5,B_6) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_146])).

tff(c_259,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | k2_tarski('#skF_5','#skF_4') != k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_255,c_149])).

tff(c_276,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_216,c_259])).

tff(c_277,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_214])).

tff(c_317,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_215,c_22])).

tff(c_91,plain,(
    ! [A_25,B_4,B_27] :
      ( ~ r2_hidden(A_25,B_4)
      | k4_xboole_0(k2_tarski(A_25,B_27),B_4) != k2_tarski(A_25,B_27) ) ),
    inference(resolution,[status(thm)],[c_6,c_80])).

tff(c_327,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_317,c_91])).

tff(c_342,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_277,c_327])).

tff(c_343,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_345,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_343])).

tff(c_344,plain,(
    r2_hidden('#skF_1','#skF_3') ),
    inference(splitRight,[status(thm)],[c_20])).

tff(c_26,plain,
    ( ~ r2_hidden('#skF_1','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_347,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_26])).

tff(c_2,plain,(
    ! [A_1,B_2] : r1_xboole_0(k4_xboole_0(A_1,B_2),B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_354,plain,(
    r1_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_2])).

tff(c_87,plain,(
    ! [A_5,C_26,B_6] :
      ( ~ r2_hidden(A_5,C_26)
      | ~ r1_xboole_0(k2_tarski(B_6,A_5),C_26) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_8,c_80])).

tff(c_361,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_354,c_87])).

tff(c_371,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_345,c_361])).

tff(c_372,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_343])).

tff(c_394,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_26])).

tff(c_401,plain,(
    r1_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_394,c_2])).

tff(c_12,plain,(
    ! [A_9,C_11,B_10] :
      ( ~ r2_hidden(A_9,C_11)
      | ~ r1_xboole_0(k2_tarski(A_9,B_10),C_11) ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_412,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_401,c_12])).

tff(c_420,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_372,c_412])).

tff(c_421,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_423,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_421])).

tff(c_422,plain,(
    r2_hidden('#skF_2','#skF_3') ),
    inference(splitRight,[status(thm)],[c_18])).

tff(c_24,plain,
    ( ~ r2_hidden('#skF_2','#skF_3')
    | k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_426,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_24])).

tff(c_433,plain,(
    r1_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_426,c_2])).

tff(c_440,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_433,c_87])).

tff(c_450,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_423,c_440])).

tff(c_451,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_421])).

tff(c_456,plain,(
    k4_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_422,c_24])).

tff(c_463,plain,(
    r1_xboole_0(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_456,c_2])).

tff(c_473,plain,(
    ~ r2_hidden('#skF_4','#skF_6') ),
    inference(resolution,[status(thm)],[c_463,c_12])).

tff(c_481,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_451,c_473])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n024.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:47:36 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.19/1.29  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.29  
% 2.19/1.29  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.30  %$ r2_hidden > r1_xboole_0 > k1_enumset1 > k4_xboole_0 > k2_tarski > #nlpp > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 2.19/1.30  
% 2.19/1.30  %Foreground sorts:
% 2.19/1.30  
% 2.19/1.30  
% 2.19/1.30  %Background operators:
% 2.19/1.30  
% 2.19/1.30  
% 2.19/1.30  %Foreground operators:
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.19/1.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.19/1.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.19/1.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.19/1.30  tff('#skF_5', type, '#skF_5': $i).
% 2.19/1.30  tff('#skF_6', type, '#skF_6': $i).
% 2.19/1.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.19/1.30  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.19/1.30  tff('#skF_2', type, '#skF_2': $i).
% 2.19/1.30  tff('#skF_3', type, '#skF_3': $i).
% 2.19/1.30  tff('#skF_1', type, '#skF_1': $i).
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.19/1.30  tff('#skF_4', type, '#skF_4': $i).
% 2.19/1.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.19/1.30  
% 2.19/1.31  tff(f_33, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 2.19/1.31  tff(f_59, negated_conjecture, ~(![A, B, C]: ((k4_xboole_0(k2_tarski(A, B), C) = k2_tarski(A, B)) <=> (~r2_hidden(A, C) & ~r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_zfmisc_1)).
% 2.19/1.31  tff(f_50, axiom, (![A, B, C]: ~((~r2_hidden(A, B) & ~r2_hidden(C, B)) & ~r1_xboole_0(k2_tarski(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t57_zfmisc_1)).
% 2.19/1.31  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 2.19/1.31  tff(f_40, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 2.19/1.31  tff(f_27, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 2.19/1.31  tff(c_8, plain, (![B_6, A_5]: (k2_tarski(B_6, A_5)=k2_tarski(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 2.19/1.31  tff(c_20, plain, (~r2_hidden('#skF_1', '#skF_3') | r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.19/1.31  tff(c_126, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(splitLeft, [status(thm)], [c_20])).
% 2.19/1.31  tff(c_18, plain, (~r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.19/1.31  tff(c_125, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(splitLeft, [status(thm)], [c_18])).
% 2.19/1.31  tff(c_127, plain, (![A_33, C_34, B_35]: (r1_xboole_0(k2_tarski(A_33, C_34), B_35) | r2_hidden(C_34, B_35) | r2_hidden(A_33, B_35))), inference(cnfTransformation, [status(thm)], [f_50])).
% 2.19/1.31  tff(c_4, plain, (![A_3, B_4]: (k4_xboole_0(A_3, B_4)=A_3 | ~r1_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.31  tff(c_175, plain, (![A_48, C_49, B_50]: (k4_xboole_0(k2_tarski(A_48, C_49), B_50)=k2_tarski(A_48, C_49) | r2_hidden(C_49, B_50) | r2_hidden(A_48, B_50))), inference(resolution, [status(thm)], [c_127, c_4])).
% 2.19/1.31  tff(c_16, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k2_tarski('#skF_1', '#skF_2') | r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_4', '#skF_6')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.19/1.31  tff(c_167, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k2_tarski('#skF_1', '#skF_2')), inference(splitLeft, [status(thm)], [c_16])).
% 2.19/1.31  tff(c_184, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_175, c_167])).
% 2.19/1.31  tff(c_213, plain, $false, inference(negUnitSimplification, [status(thm)], [c_126, c_125, c_184])).
% 2.19/1.31  tff(c_214, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_16])).
% 2.19/1.31  tff(c_216, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_214])).
% 2.19/1.31  tff(c_215, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')=k2_tarski('#skF_1', '#skF_2')), inference(splitRight, [status(thm)], [c_16])).
% 2.19/1.31  tff(c_22, plain, (k4_xboole_0(k2_tarski('#skF_1', '#skF_2'), '#skF_3')!=k2_tarski('#skF_1', '#skF_2') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.19/1.31  tff(c_255, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_22])).
% 2.19/1.31  tff(c_6, plain, (![A_3, B_4]: (r1_xboole_0(A_3, B_4) | k4_xboole_0(A_3, B_4)!=A_3)), inference(cnfTransformation, [status(thm)], [f_31])).
% 2.19/1.31  tff(c_80, plain, (![A_25, C_26, B_27]: (~r2_hidden(A_25, C_26) | ~r1_xboole_0(k2_tarski(A_25, B_27), C_26))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.19/1.31  tff(c_146, plain, (![A_36, B_37, B_38]: (~r2_hidden(A_36, B_37) | k4_xboole_0(k2_tarski(A_36, B_38), B_37)!=k2_tarski(A_36, B_38))), inference(resolution, [status(thm)], [c_6, c_80])).
% 2.19/1.31  tff(c_149, plain, (![A_5, B_37, B_6]: (~r2_hidden(A_5, B_37) | k4_xboole_0(k2_tarski(B_6, A_5), B_37)!=k2_tarski(A_5, B_6))), inference(superposition, [status(thm), theory('equality')], [c_8, c_146])).
% 2.19/1.31  tff(c_259, plain, (~r2_hidden('#skF_5', '#skF_6') | k2_tarski('#skF_5', '#skF_4')!=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_255, c_149])).
% 2.19/1.31  tff(c_276, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_216, c_259])).
% 2.19/1.31  tff(c_277, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_214])).
% 2.19/1.31  tff(c_317, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_215, c_22])).
% 2.19/1.31  tff(c_91, plain, (![A_25, B_4, B_27]: (~r2_hidden(A_25, B_4) | k4_xboole_0(k2_tarski(A_25, B_27), B_4)!=k2_tarski(A_25, B_27))), inference(resolution, [status(thm)], [c_6, c_80])).
% 2.19/1.31  tff(c_327, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_317, c_91])).
% 2.19/1.31  tff(c_342, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_277, c_327])).
% 2.19/1.31  tff(c_343, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_20])).
% 2.19/1.31  tff(c_345, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_343])).
% 2.19/1.31  tff(c_344, plain, (r2_hidden('#skF_1', '#skF_3')), inference(splitRight, [status(thm)], [c_20])).
% 2.19/1.31  tff(c_26, plain, (~r2_hidden('#skF_1', '#skF_3') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.19/1.31  tff(c_347, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_344, c_26])).
% 2.19/1.31  tff(c_2, plain, (![A_1, B_2]: (r1_xboole_0(k4_xboole_0(A_1, B_2), B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.19/1.31  tff(c_354, plain, (r1_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_347, c_2])).
% 2.19/1.31  tff(c_87, plain, (![A_5, C_26, B_6]: (~r2_hidden(A_5, C_26) | ~r1_xboole_0(k2_tarski(B_6, A_5), C_26))), inference(superposition, [status(thm), theory('equality')], [c_8, c_80])).
% 2.19/1.31  tff(c_361, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_354, c_87])).
% 2.19/1.31  tff(c_371, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_345, c_361])).
% 2.19/1.31  tff(c_372, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_343])).
% 2.19/1.31  tff(c_394, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_344, c_26])).
% 2.19/1.31  tff(c_401, plain, (r1_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_394, c_2])).
% 2.19/1.31  tff(c_12, plain, (![A_9, C_11, B_10]: (~r2_hidden(A_9, C_11) | ~r1_xboole_0(k2_tarski(A_9, B_10), C_11))), inference(cnfTransformation, [status(thm)], [f_40])).
% 2.19/1.31  tff(c_412, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_401, c_12])).
% 2.19/1.31  tff(c_420, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_372, c_412])).
% 2.19/1.31  tff(c_421, plain, (r2_hidden('#skF_4', '#skF_6') | r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_18])).
% 2.19/1.31  tff(c_423, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_421])).
% 2.19/1.31  tff(c_422, plain, (r2_hidden('#skF_2', '#skF_3')), inference(splitRight, [status(thm)], [c_18])).
% 2.19/1.31  tff(c_24, plain, (~r2_hidden('#skF_2', '#skF_3') | k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.19/1.31  tff(c_426, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_422, c_24])).
% 2.19/1.31  tff(c_433, plain, (r1_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_426, c_2])).
% 2.19/1.31  tff(c_440, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_433, c_87])).
% 2.19/1.31  tff(c_450, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_423, c_440])).
% 2.19/1.31  tff(c_451, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_421])).
% 2.19/1.31  tff(c_456, plain, (k4_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_422, c_24])).
% 2.19/1.31  tff(c_463, plain, (r1_xboole_0(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_456, c_2])).
% 2.19/1.31  tff(c_473, plain, (~r2_hidden('#skF_4', '#skF_6')), inference(resolution, [status(thm)], [c_463, c_12])).
% 2.19/1.31  tff(c_481, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_451, c_473])).
% 2.19/1.31  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.19/1.31  
% 2.19/1.31  Inference rules
% 2.19/1.31  ----------------------
% 2.19/1.31  #Ref     : 0
% 2.19/1.31  #Sup     : 114
% 2.19/1.31  #Fact    : 0
% 2.19/1.31  #Define  : 0
% 2.19/1.31  #Split   : 7
% 2.19/1.31  #Chain   : 0
% 2.19/1.31  #Close   : 0
% 2.19/1.31  
% 2.19/1.31  Ordering : KBO
% 2.19/1.31  
% 2.19/1.31  Simplification rules
% 2.19/1.31  ----------------------
% 2.19/1.31  #Subsume      : 31
% 2.19/1.31  #Demod        : 37
% 2.19/1.31  #Tautology    : 45
% 2.19/1.31  #SimpNegUnit  : 2
% 2.19/1.31  #BackRed      : 0
% 2.19/1.31  
% 2.19/1.31  #Partial instantiations: 0
% 2.19/1.31  #Strategies tried      : 1
% 2.19/1.31  
% 2.19/1.31  Timing (in seconds)
% 2.19/1.31  ----------------------
% 2.19/1.31  Preprocessing        : 0.29
% 2.19/1.31  Parsing              : 0.15
% 2.19/1.31  CNF conversion       : 0.02
% 2.19/1.31  Main loop            : 0.24
% 2.19/1.31  Inferencing          : 0.09
% 2.19/1.31  Reduction            : 0.08
% 2.19/1.31  Demodulation         : 0.06
% 2.19/1.31  BG Simplification    : 0.01
% 2.19/1.31  Subsumption          : 0.04
% 2.19/1.31  Abstraction          : 0.01
% 2.19/1.31  MUC search           : 0.00
% 2.19/1.32  Cooper               : 0.00
% 2.19/1.32  Total                : 0.56
% 2.19/1.32  Index Insertion      : 0.00
% 2.19/1.32  Index Deletion       : 0.00
% 2.19/1.32  Index Matching       : 0.00
% 2.19/1.32  BG Taut test         : 0.00
%------------------------------------------------------------------------------

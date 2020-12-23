%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n004.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:56 EST 2020

% Result     : Theorem 3.80s
% Output     : CNFRefutation 3.80s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 186 expanded)
%              Number of leaves         :   18 (  64 expanded)
%              Depth                    :    9
%              Number of atoms          :  101 ( 373 expanded)
%              Number of equality atoms :   19 (  46 expanded)
%              Maximal formula depth    :    8 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k2_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_48,negated_conjecture,(
    ~ ! [A,B,C] :
        ( r1_tarski(k2_tarski(A,B),C)
      <=> ( r2_hidden(A,C)
          & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d3_tarski)).

tff(c_28,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_49,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_28])).

tff(c_34,plain,
    ( r2_hidden('#skF_5','#skF_6')
    | r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_39,plain,(
    r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_34])).

tff(c_12,plain,(
    ! [D_11,B_7] : r2_hidden(D_11,k2_tarski(D_11,B_7)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_67,plain,(
    ! [C_24,B_25,A_26] :
      ( r2_hidden(C_24,B_25)
      | ~ r2_hidden(C_24,A_26)
      | ~ r1_tarski(A_26,B_25) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_101,plain,(
    ! [D_31,B_32,B_33] :
      ( r2_hidden(D_31,B_32)
      | ~ r1_tarski(k2_tarski(D_31,B_33),B_32) ) ),
    inference(resolution,[status(thm)],[c_12,c_67])).

tff(c_108,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(resolution,[status(thm)],[c_39,c_101])).

tff(c_114,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_49,c_108])).

tff(c_116,plain,(
    r2_hidden('#skF_7','#skF_9') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_30,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | ~ r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_117,plain,(
    ~ r2_hidden('#skF_7','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_30])).

tff(c_119,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_117])).

tff(c_120,plain,
    ( ~ r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_30])).

tff(c_123,plain,(
    ~ r2_hidden('#skF_8','#skF_9') ),
    inference(splitLeft,[status(thm)],[c_120])).

tff(c_10,plain,(
    ! [D_11,A_6] : r2_hidden(D_11,k2_tarski(A_6,D_11)) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_124,plain,(
    ! [C_34,B_35,A_36] :
      ( r2_hidden(C_34,B_35)
      | ~ r2_hidden(C_34,A_36)
      | ~ r1_tarski(A_36,B_35) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_142,plain,(
    ! [D_38,B_39,A_40] :
      ( r2_hidden(D_38,B_39)
      | ~ r1_tarski(k2_tarski(A_40,D_38),B_39) ) ),
    inference(resolution,[status(thm)],[c_10,c_124])).

tff(c_149,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(resolution,[status(thm)],[c_39,c_142])).

tff(c_155,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_123,c_149])).

tff(c_157,plain,(
    r2_hidden('#skF_8','#skF_9') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_26,plain,
    ( ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | ~ r2_hidden('#skF_8','#skF_9')
    | ~ r2_hidden('#skF_7','#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_269,plain,(
    ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_116,c_157,c_26])).

tff(c_115,plain,
    ( ~ r2_hidden('#skF_8','#skF_9')
    | r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_28])).

tff(c_159,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_157,c_115])).

tff(c_156,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_120])).

tff(c_6,plain,(
    ! [A_1,B_2] :
      ( r2_hidden('#skF_1'(A_1,B_2),A_1)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_160,plain,(
    ! [D_41,B_42,A_43] :
      ( D_41 = B_42
      | D_41 = A_43
      | ~ r2_hidden(D_41,k2_tarski(A_43,B_42)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_360,plain,(
    ! [A_101,B_102,B_103] :
      ( '#skF_1'(k2_tarski(A_101,B_102),B_103) = B_102
      | '#skF_1'(k2_tarski(A_101,B_102),B_103) = A_101
      | r1_tarski(k2_tarski(A_101,B_102),B_103) ) ),
    inference(resolution,[status(thm)],[c_6,c_160])).

tff(c_393,plain,
    ( '#skF_1'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_5'
    | '#skF_1'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_360,c_269])).

tff(c_800,plain,(
    '#skF_1'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_393])).

tff(c_4,plain,(
    ! [A_1,B_2] :
      ( ~ r2_hidden('#skF_1'(A_1,B_2),B_2)
      | r1_tarski(A_1,B_2) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_813,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_800,c_4])).

tff(c_863,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_156,c_813])).

tff(c_865,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_863])).

tff(c_866,plain,(
    '#skF_1'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_393])).

tff(c_880,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_866,c_4])).

tff(c_930,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_159,c_880])).

tff(c_932,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_269,c_930])).

tff(c_934,plain,(
    ~ r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_32,plain,
    ( ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6')
    | r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_1014,plain,(
    ~ r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(negUnitSimplification,[status(thm)],[c_934,c_32])).

tff(c_933,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_34])).

tff(c_36,plain,
    ( r2_hidden('#skF_4','#skF_6')
    | r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_935,plain,(
    r1_tarski(k2_tarski('#skF_7','#skF_8'),'#skF_9') ),
    inference(splitLeft,[status(thm)],[c_36])).

tff(c_936,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_934,c_935])).

tff(c_937,plain,(
    r2_hidden('#skF_4','#skF_6') ),
    inference(splitRight,[status(thm)],[c_36])).

tff(c_973,plain,(
    ! [D_570,B_571,A_572] :
      ( D_570 = B_571
      | D_570 = A_572
      | ~ r2_hidden(D_570,k2_tarski(A_572,B_571)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_2519,plain,(
    ! [A_1826,B_1827,B_1828] :
      ( '#skF_1'(k2_tarski(A_1826,B_1827),B_1828) = B_1827
      | '#skF_1'(k2_tarski(A_1826,B_1827),B_1828) = A_1826
      | r1_tarski(k2_tarski(A_1826,B_1827),B_1828) ) ),
    inference(resolution,[status(thm)],[c_6,c_973])).

tff(c_2732,plain,
    ( '#skF_1'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_5'
    | '#skF_1'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_4' ),
    inference(resolution,[status(thm)],[c_2519,c_1014])).

tff(c_2736,plain,(
    '#skF_1'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_4' ),
    inference(splitLeft,[status(thm)],[c_2732])).

tff(c_2743,plain,
    ( ~ r2_hidden('#skF_4','#skF_6')
    | r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2736,c_4])).

tff(c_2843,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_937,c_2743])).

tff(c_2845,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1014,c_2843])).

tff(c_2846,plain,(
    '#skF_1'(k2_tarski('#skF_4','#skF_5'),'#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_2732])).

tff(c_2854,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2846,c_4])).

tff(c_2954,plain,(
    r1_tarski(k2_tarski('#skF_4','#skF_5'),'#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_933,c_2854])).

tff(c_2956,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1014,c_2954])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n004.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 15:40:08 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.80/1.71  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.71  
% 3.80/1.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.72  %$ r2_hidden > r1_tarski > k2_tarski > #nlpp > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_9 > #skF_8 > #skF_4 > #skF_3 > #skF_1
% 3.80/1.72  
% 3.80/1.72  %Foreground sorts:
% 3.80/1.72  
% 3.80/1.72  
% 3.80/1.72  %Background operators:
% 3.80/1.72  
% 3.80/1.72  
% 3.80/1.72  %Foreground operators:
% 3.80/1.72  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.80/1.72  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.80/1.72  tff('#skF_7', type, '#skF_7': $i).
% 3.80/1.72  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.80/1.72  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.80/1.72  tff('#skF_5', type, '#skF_5': $i).
% 3.80/1.72  tff('#skF_6', type, '#skF_6': $i).
% 3.80/1.72  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.80/1.72  tff('#skF_9', type, '#skF_9': $i).
% 3.80/1.72  tff('#skF_8', type, '#skF_8': $i).
% 3.80/1.72  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.80/1.72  tff('#skF_4', type, '#skF_4': $i).
% 3.80/1.72  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.80/1.72  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.80/1.72  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.80/1.72  
% 3.80/1.73  tff(f_48, negated_conjecture, ~(![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 3.80/1.73  tff(f_41, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.80/1.73  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d3_tarski)).
% 3.80/1.73  tff(c_28, plain, (r2_hidden('#skF_5', '#skF_6') | ~r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.80/1.73  tff(c_49, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_28])).
% 3.80/1.73  tff(c_34, plain, (r2_hidden('#skF_5', '#skF_6') | r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.80/1.73  tff(c_39, plain, (r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(splitLeft, [status(thm)], [c_34])).
% 3.80/1.73  tff(c_12, plain, (![D_11, B_7]: (r2_hidden(D_11, k2_tarski(D_11, B_7)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.80/1.73  tff(c_67, plain, (![C_24, B_25, A_26]: (r2_hidden(C_24, B_25) | ~r2_hidden(C_24, A_26) | ~r1_tarski(A_26, B_25))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.80/1.73  tff(c_101, plain, (![D_31, B_32, B_33]: (r2_hidden(D_31, B_32) | ~r1_tarski(k2_tarski(D_31, B_33), B_32))), inference(resolution, [status(thm)], [c_12, c_67])).
% 3.80/1.73  tff(c_108, plain, (r2_hidden('#skF_7', '#skF_9')), inference(resolution, [status(thm)], [c_39, c_101])).
% 3.80/1.73  tff(c_114, plain, $false, inference(negUnitSimplification, [status(thm)], [c_49, c_108])).
% 3.80/1.73  tff(c_116, plain, (r2_hidden('#skF_7', '#skF_9')), inference(splitRight, [status(thm)], [c_28])).
% 3.80/1.73  tff(c_30, plain, (r2_hidden('#skF_4', '#skF_6') | ~r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.80/1.73  tff(c_117, plain, (~r2_hidden('#skF_7', '#skF_9')), inference(splitLeft, [status(thm)], [c_30])).
% 3.80/1.73  tff(c_119, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_116, c_117])).
% 3.80/1.73  tff(c_120, plain, (~r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_30])).
% 3.80/1.73  tff(c_123, plain, (~r2_hidden('#skF_8', '#skF_9')), inference(splitLeft, [status(thm)], [c_120])).
% 3.80/1.73  tff(c_10, plain, (![D_11, A_6]: (r2_hidden(D_11, k2_tarski(A_6, D_11)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.80/1.73  tff(c_124, plain, (![C_34, B_35, A_36]: (r2_hidden(C_34, B_35) | ~r2_hidden(C_34, A_36) | ~r1_tarski(A_36, B_35))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.80/1.73  tff(c_142, plain, (![D_38, B_39, A_40]: (r2_hidden(D_38, B_39) | ~r1_tarski(k2_tarski(A_40, D_38), B_39))), inference(resolution, [status(thm)], [c_10, c_124])).
% 3.80/1.73  tff(c_149, plain, (r2_hidden('#skF_8', '#skF_9')), inference(resolution, [status(thm)], [c_39, c_142])).
% 3.80/1.73  tff(c_155, plain, $false, inference(negUnitSimplification, [status(thm)], [c_123, c_149])).
% 3.80/1.73  tff(c_157, plain, (r2_hidden('#skF_8', '#skF_9')), inference(splitRight, [status(thm)], [c_120])).
% 3.80/1.73  tff(c_26, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | ~r2_hidden('#skF_8', '#skF_9') | ~r2_hidden('#skF_7', '#skF_9')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.80/1.73  tff(c_269, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_116, c_157, c_26])).
% 3.80/1.73  tff(c_115, plain, (~r2_hidden('#skF_8', '#skF_9') | r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_28])).
% 3.80/1.73  tff(c_159, plain, (r2_hidden('#skF_5', '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_157, c_115])).
% 3.80/1.73  tff(c_156, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_120])).
% 3.80/1.73  tff(c_6, plain, (![A_1, B_2]: (r2_hidden('#skF_1'(A_1, B_2), A_1) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.80/1.73  tff(c_160, plain, (![D_41, B_42, A_43]: (D_41=B_42 | D_41=A_43 | ~r2_hidden(D_41, k2_tarski(A_43, B_42)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.80/1.73  tff(c_360, plain, (![A_101, B_102, B_103]: ('#skF_1'(k2_tarski(A_101, B_102), B_103)=B_102 | '#skF_1'(k2_tarski(A_101, B_102), B_103)=A_101 | r1_tarski(k2_tarski(A_101, B_102), B_103))), inference(resolution, [status(thm)], [c_6, c_160])).
% 3.80/1.73  tff(c_393, plain, ('#skF_1'(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_5' | '#skF_1'(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_360, c_269])).
% 3.80/1.73  tff(c_800, plain, ('#skF_1'(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_393])).
% 3.80/1.73  tff(c_4, plain, (![A_1, B_2]: (~r2_hidden('#skF_1'(A_1, B_2), B_2) | r1_tarski(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.80/1.73  tff(c_813, plain, (~r2_hidden('#skF_4', '#skF_6') | r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_800, c_4])).
% 3.80/1.73  tff(c_863, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_156, c_813])).
% 3.80/1.73  tff(c_865, plain, $false, inference(negUnitSimplification, [status(thm)], [c_269, c_863])).
% 3.80/1.73  tff(c_866, plain, ('#skF_1'(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_393])).
% 3.80/1.73  tff(c_880, plain, (~r2_hidden('#skF_5', '#skF_6') | r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_866, c_4])).
% 3.80/1.73  tff(c_930, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_159, c_880])).
% 3.80/1.73  tff(c_932, plain, $false, inference(negUnitSimplification, [status(thm)], [c_269, c_930])).
% 3.80/1.73  tff(c_934, plain, (~r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(splitRight, [status(thm)], [c_34])).
% 3.80/1.73  tff(c_32, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6') | r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.80/1.73  tff(c_1014, plain, (~r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(negUnitSimplification, [status(thm)], [c_934, c_32])).
% 3.80/1.73  tff(c_933, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_34])).
% 3.80/1.73  tff(c_36, plain, (r2_hidden('#skF_4', '#skF_6') | r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.80/1.73  tff(c_935, plain, (r1_tarski(k2_tarski('#skF_7', '#skF_8'), '#skF_9')), inference(splitLeft, [status(thm)], [c_36])).
% 3.80/1.73  tff(c_936, plain, $false, inference(negUnitSimplification, [status(thm)], [c_934, c_935])).
% 3.80/1.73  tff(c_937, plain, (r2_hidden('#skF_4', '#skF_6')), inference(splitRight, [status(thm)], [c_36])).
% 3.80/1.73  tff(c_973, plain, (![D_570, B_571, A_572]: (D_570=B_571 | D_570=A_572 | ~r2_hidden(D_570, k2_tarski(A_572, B_571)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.80/1.73  tff(c_2519, plain, (![A_1826, B_1827, B_1828]: ('#skF_1'(k2_tarski(A_1826, B_1827), B_1828)=B_1827 | '#skF_1'(k2_tarski(A_1826, B_1827), B_1828)=A_1826 | r1_tarski(k2_tarski(A_1826, B_1827), B_1828))), inference(resolution, [status(thm)], [c_6, c_973])).
% 3.80/1.73  tff(c_2732, plain, ('#skF_1'(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_5' | '#skF_1'(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_4'), inference(resolution, [status(thm)], [c_2519, c_1014])).
% 3.80/1.73  tff(c_2736, plain, ('#skF_1'(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_4'), inference(splitLeft, [status(thm)], [c_2732])).
% 3.80/1.73  tff(c_2743, plain, (~r2_hidden('#skF_4', '#skF_6') | r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2736, c_4])).
% 3.80/1.73  tff(c_2843, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_937, c_2743])).
% 3.80/1.73  tff(c_2845, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1014, c_2843])).
% 3.80/1.73  tff(c_2846, plain, ('#skF_1'(k2_tarski('#skF_4', '#skF_5'), '#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_2732])).
% 3.80/1.73  tff(c_2854, plain, (~r2_hidden('#skF_5', '#skF_6') | r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2846, c_4])).
% 3.80/1.73  tff(c_2954, plain, (r1_tarski(k2_tarski('#skF_4', '#skF_5'), '#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_933, c_2854])).
% 3.80/1.73  tff(c_2956, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1014, c_2954])).
% 3.80/1.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.80/1.73  
% 3.80/1.73  Inference rules
% 3.80/1.73  ----------------------
% 3.80/1.73  #Ref     : 0
% 3.80/1.73  #Sup     : 460
% 3.80/1.73  #Fact    : 6
% 3.80/1.73  #Define  : 0
% 3.80/1.73  #Split   : 11
% 3.80/1.73  #Chain   : 0
% 3.80/1.73  #Close   : 0
% 3.80/1.73  
% 3.80/1.73  Ordering : KBO
% 3.80/1.73  
% 3.80/1.73  Simplification rules
% 3.80/1.73  ----------------------
% 3.80/1.73  #Subsume      : 47
% 3.80/1.73  #Demod        : 28
% 3.80/1.73  #Tautology    : 80
% 3.80/1.73  #SimpNegUnit  : 16
% 3.80/1.73  #BackRed      : 0
% 3.80/1.73  
% 3.80/1.73  #Partial instantiations: 1720
% 3.80/1.73  #Strategies tried      : 1
% 3.80/1.73  
% 3.80/1.73  Timing (in seconds)
% 3.80/1.73  ----------------------
% 3.80/1.73  Preprocessing        : 0.27
% 3.80/1.73  Parsing              : 0.14
% 3.80/1.73  CNF conversion       : 0.02
% 3.80/1.73  Main loop            : 0.64
% 3.80/1.73  Inferencing          : 0.32
% 3.80/1.73  Reduction            : 0.13
% 3.80/1.73  Demodulation         : 0.09
% 3.80/1.73  BG Simplification    : 0.04
% 3.80/1.73  Subsumption          : 0.11
% 3.80/1.73  Abstraction          : 0.03
% 3.80/1.73  MUC search           : 0.00
% 3.80/1.73  Cooper               : 0.00
% 3.80/1.73  Total                : 0.94
% 3.80/1.73  Index Insertion      : 0.00
% 3.80/1.73  Index Deletion       : 0.00
% 3.80/1.73  Index Matching       : 0.00
% 3.80/1.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------

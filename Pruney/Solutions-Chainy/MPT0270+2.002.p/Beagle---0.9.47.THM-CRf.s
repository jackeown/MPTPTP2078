%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:52:53 EST 2020

% Result     : Theorem 3.96s
% Output     : CNFRefutation 3.96s
% Verified   : 
% Statistics : Number of formulae       :   59 (  77 expanded)
%              Number of leaves         :   28 (  39 expanded)
%              Depth                    :    6
%              Number of atoms          :   52 (  84 expanded)
%              Number of equality atoms :   15 (  29 expanded)
%              Maximal formula depth    :    7 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(f_107,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_tarski(A)
      <=> ~ r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_zfmisc_1)).

tff(f_96,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_77,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_85,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_101,axiom,(
    ! [A,B,C] :
      ~ ( r1_xboole_0(k2_tarski(A,B),C)
        & r2_hidden(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t55_zfmisc_1)).

tff(c_70,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_99,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_64,plain,(
    ! [A_41,B_42] :
      ( r1_xboole_0(k1_tarski(A_41),B_42)
      | r2_hidden(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_96])).

tff(c_192,plain,(
    ! [A_63,B_64] :
      ( k4_xboole_0(A_63,B_64) = A_63
      | ~ r1_xboole_0(A_63,B_64) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_2057,plain,(
    ! [A_197,B_198] :
      ( k4_xboole_0(k1_tarski(A_197),B_198) = k1_tarski(A_197)
      | r2_hidden(A_197,B_198) ) ),
    inference(resolution,[status(thm)],[c_64,c_192])).

tff(c_68,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5')
    | r2_hidden('#skF_7','#skF_8') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_297,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_2103,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_2057,c_297])).

tff(c_2146,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_99,c_2103])).

tff(c_2147,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_2148,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_tarski('#skF_5') ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_72,plain,
    ( k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5')
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_2149,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') != k1_tarski('#skF_5') ),
    inference(splitLeft,[status(thm)],[c_72])).

tff(c_2197,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2148,c_2149])).

tff(c_2198,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_72])).

tff(c_48,plain,(
    ! [A_25,B_26] : r1_xboole_0(k4_xboole_0(A_25,B_26),B_26) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_2257,plain,(
    r1_xboole_0(k1_tarski('#skF_7'),'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_2198,c_48])).

tff(c_56,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_2542,plain,(
    ! [A_219,C_220,B_221] :
      ( ~ r2_hidden(A_219,C_220)
      | ~ r1_xboole_0(k2_tarski(A_219,B_221),C_220) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_2874,plain,(
    ! [A_235,C_236] :
      ( ~ r2_hidden(A_235,C_236)
      | ~ r1_xboole_0(k1_tarski(A_235),C_236) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2542])).

tff(c_2885,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_2257,c_2874])).

tff(c_2909,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2147,c_2885])).

tff(c_2910,plain,(
    r2_hidden('#skF_7','#skF_8') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_2911,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_74,plain,
    ( ~ r2_hidden('#skF_5','#skF_6')
    | k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_107])).

tff(c_3001,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),'#skF_8') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2911,c_74])).

tff(c_3008,plain,(
    r1_xboole_0(k1_tarski('#skF_7'),'#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3001,c_48])).

tff(c_3175,plain,(
    ! [A_262,C_263,B_264] :
      ( ~ r2_hidden(A_262,C_263)
      | ~ r1_xboole_0(k2_tarski(A_262,B_264),C_263) ) ),
    inference(cnfTransformation,[status(thm)],[f_101])).

tff(c_3229,plain,(
    ! [A_269,C_270] :
      ( ~ r2_hidden(A_269,C_270)
      | ~ r1_xboole_0(k1_tarski(A_269),C_270) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_3175])).

tff(c_3247,plain,(
    ~ r2_hidden('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_3008,c_3229])).

tff(c_3263,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_2910,c_3247])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:12:38 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.96/1.69  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.70  
% 3.96/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.70  %$ r2_hidden > r1_xboole_0 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_4 > #skF_7 > #skF_3 > #skF_5 > #skF_6 > #skF_2 > #skF_8
% 3.96/1.70  
% 3.96/1.70  %Foreground sorts:
% 3.96/1.70  
% 3.96/1.70  
% 3.96/1.70  %Background operators:
% 3.96/1.70  
% 3.96/1.70  
% 3.96/1.70  %Foreground operators:
% 3.96/1.70  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.96/1.70  tff('#skF_4', type, '#skF_4': $i > $i).
% 3.96/1.70  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.96/1.70  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.96/1.70  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.96/1.70  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.96/1.70  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.96/1.70  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.96/1.70  tff('#skF_7', type, '#skF_7': $i).
% 3.96/1.70  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.96/1.70  tff('#skF_3', type, '#skF_3': ($i * $i) > $i).
% 3.96/1.70  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.96/1.70  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.96/1.70  tff('#skF_5', type, '#skF_5': $i).
% 3.96/1.70  tff('#skF_6', type, '#skF_6': $i).
% 3.96/1.70  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.96/1.70  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.96/1.70  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.96/1.70  tff('#skF_8', type, '#skF_8': $i).
% 3.96/1.70  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.96/1.70  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.96/1.70  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.96/1.70  
% 3.96/1.71  tff(f_107, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)) <=> ~r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_zfmisc_1)).
% 3.96/1.71  tff(f_96, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 3.96/1.71  tff(f_81, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.96/1.71  tff(f_77, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.96/1.71  tff(f_85, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.96/1.71  tff(f_101, axiom, (![A, B, C]: ~(r1_xboole_0(k2_tarski(A, B), C) & r2_hidden(A, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t55_zfmisc_1)).
% 3.96/1.71  tff(c_70, plain, (~r2_hidden('#skF_5', '#skF_6') | r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.96/1.71  tff(c_99, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_70])).
% 3.96/1.71  tff(c_64, plain, (![A_41, B_42]: (r1_xboole_0(k1_tarski(A_41), B_42) | r2_hidden(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_96])).
% 3.96/1.71  tff(c_192, plain, (![A_63, B_64]: (k4_xboole_0(A_63, B_64)=A_63 | ~r1_xboole_0(A_63, B_64))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.96/1.71  tff(c_2057, plain, (![A_197, B_198]: (k4_xboole_0(k1_tarski(A_197), B_198)=k1_tarski(A_197) | r2_hidden(A_197, B_198))), inference(resolution, [status(thm)], [c_64, c_192])).
% 3.96/1.71  tff(c_68, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5') | r2_hidden('#skF_7', '#skF_8')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.96/1.71  tff(c_297, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_68])).
% 3.96/1.71  tff(c_2103, plain, (r2_hidden('#skF_5', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2057, c_297])).
% 3.96/1.71  tff(c_2146, plain, $false, inference(negUnitSimplification, [status(thm)], [c_99, c_2103])).
% 3.96/1.71  tff(c_2147, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_68])).
% 3.96/1.71  tff(c_2148, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_tarski('#skF_5')), inference(splitRight, [status(thm)], [c_68])).
% 3.96/1.71  tff(c_72, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5') | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.96/1.71  tff(c_2149, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')!=k1_tarski('#skF_5')), inference(splitLeft, [status(thm)], [c_72])).
% 3.96/1.71  tff(c_2197, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2148, c_2149])).
% 3.96/1.71  tff(c_2198, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_72])).
% 3.96/1.71  tff(c_48, plain, (![A_25, B_26]: (r1_xboole_0(k4_xboole_0(A_25, B_26), B_26))), inference(cnfTransformation, [status(thm)], [f_77])).
% 3.96/1.71  tff(c_2257, plain, (r1_xboole_0(k1_tarski('#skF_7'), '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_2198, c_48])).
% 3.96/1.71  tff(c_56, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_85])).
% 3.96/1.71  tff(c_2542, plain, (![A_219, C_220, B_221]: (~r2_hidden(A_219, C_220) | ~r1_xboole_0(k2_tarski(A_219, B_221), C_220))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.96/1.71  tff(c_2874, plain, (![A_235, C_236]: (~r2_hidden(A_235, C_236) | ~r1_xboole_0(k1_tarski(A_235), C_236))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2542])).
% 3.96/1.71  tff(c_2885, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_2257, c_2874])).
% 3.96/1.71  tff(c_2909, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2147, c_2885])).
% 3.96/1.71  tff(c_2910, plain, (r2_hidden('#skF_7', '#skF_8')), inference(splitRight, [status(thm)], [c_70])).
% 3.96/1.71  tff(c_2911, plain, (r2_hidden('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_70])).
% 3.96/1.71  tff(c_74, plain, (~r2_hidden('#skF_5', '#skF_6') | k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_107])).
% 3.96/1.71  tff(c_3001, plain, (k4_xboole_0(k1_tarski('#skF_7'), '#skF_8')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_2911, c_74])).
% 3.96/1.71  tff(c_3008, plain, (r1_xboole_0(k1_tarski('#skF_7'), '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3001, c_48])).
% 3.96/1.71  tff(c_3175, plain, (![A_262, C_263, B_264]: (~r2_hidden(A_262, C_263) | ~r1_xboole_0(k2_tarski(A_262, B_264), C_263))), inference(cnfTransformation, [status(thm)], [f_101])).
% 3.96/1.71  tff(c_3229, plain, (![A_269, C_270]: (~r2_hidden(A_269, C_270) | ~r1_xboole_0(k1_tarski(A_269), C_270))), inference(superposition, [status(thm), theory('equality')], [c_56, c_3175])).
% 3.96/1.71  tff(c_3247, plain, (~r2_hidden('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_3008, c_3229])).
% 3.96/1.71  tff(c_3263, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_2910, c_3247])).
% 3.96/1.71  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.96/1.71  
% 3.96/1.71  Inference rules
% 3.96/1.71  ----------------------
% 3.96/1.71  #Ref     : 0
% 3.96/1.71  #Sup     : 759
% 3.96/1.71  #Fact    : 0
% 3.96/1.71  #Define  : 0
% 3.96/1.71  #Split   : 3
% 3.96/1.71  #Chain   : 0
% 3.96/1.71  #Close   : 0
% 3.96/1.71  
% 3.96/1.71  Ordering : KBO
% 3.96/1.71  
% 3.96/1.71  Simplification rules
% 3.96/1.71  ----------------------
% 3.96/1.71  #Subsume      : 151
% 3.96/1.71  #Demod        : 251
% 3.96/1.71  #Tautology    : 368
% 3.96/1.71  #SimpNegUnit  : 38
% 3.96/1.71  #BackRed      : 0
% 3.96/1.71  
% 3.96/1.71  #Partial instantiations: 0
% 3.96/1.71  #Strategies tried      : 1
% 3.96/1.71  
% 3.96/1.71  Timing (in seconds)
% 3.96/1.71  ----------------------
% 3.96/1.71  Preprocessing        : 0.34
% 3.96/1.71  Parsing              : 0.17
% 3.96/1.71  CNF conversion       : 0.03
% 3.96/1.71  Main loop            : 0.61
% 3.96/1.71  Inferencing          : 0.22
% 3.96/1.71  Reduction            : 0.21
% 3.96/1.71  Demodulation         : 0.16
% 3.96/1.71  BG Simplification    : 0.03
% 3.96/1.71  Subsumption          : 0.11
% 3.96/1.71  Abstraction          : 0.04
% 3.96/1.71  MUC search           : 0.00
% 3.96/1.71  Cooper               : 0.00
% 3.96/1.71  Total                : 0.99
% 3.96/1.71  Index Insertion      : 0.00
% 3.96/1.71  Index Deletion       : 0.00
% 3.96/1.71  Index Matching       : 0.00
% 3.96/1.71  BG Taut test         : 0.00
%------------------------------------------------------------------------------

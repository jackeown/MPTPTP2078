%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:57 EST 2020

% Result     : Theorem 9.66s
% Output     : CNFRefutation 9.80s
% Verified   : 
% Statistics : Number of formulae       :   60 (  82 expanded)
%              Number of leaves         :   30 (  42 expanded)
%              Depth                    :   10
%              Number of atoms          :   54 (  93 expanded)
%              Number of equality atoms :   37 (  62 expanded)
%              Maximal formula depth    :    9 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_81,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_60,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r2_hidden(C,B) )
     => k3_xboole_0(k2_tarski(A,C),B) = k2_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t53_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_48,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_52,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_50,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_56,axiom,(
    ! [A,B] : k4_xboole_0(A,k3_xboole_0(A,B)) = k4_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t47_xboole_1)).

tff(c_50,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_52,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_40,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_1758,plain,(
    ! [A_122,C_123,B_124] :
      ( k3_xboole_0(k2_tarski(A_122,C_123),B_124) = k2_tarski(A_122,C_123)
      | ~ r2_hidden(C_123,B_124)
      | ~ r2_hidden(A_122,B_124) ) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1845,plain,(
    ! [A_26,B_124] :
      ( k3_xboole_0(k1_tarski(A_26),B_124) = k2_tarski(A_26,A_26)
      | ~ r2_hidden(A_26,B_124)
      | ~ r2_hidden(A_26,B_124) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1758])).

tff(c_15961,plain,(
    ! [A_296,B_297] :
      ( k3_xboole_0(k1_tarski(A_296),B_297) = k1_tarski(A_296)
      | ~ r2_hidden(A_296,B_297)
      | ~ r2_hidden(A_296,B_297) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1845])).

tff(c_79,plain,(
    ! [B_41,A_42] : k3_xboole_0(B_41,A_42) = k3_xboole_0(A_42,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_54,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_94,plain,(
    k3_xboole_0('#skF_6','#skF_5') = k1_tarski('#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_79,c_54])).

tff(c_56,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_149,plain,(
    ! [A_47,B_48] :
      ( k2_xboole_0(A_47,B_48) = B_48
      | ~ r1_tarski(A_47,B_48) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_153,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_56,c_149])).

tff(c_32,plain,(
    ! [A_19,B_20] : k3_xboole_0(A_19,k2_xboole_0(A_19,B_20)) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_157,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_153,c_32])).

tff(c_861,plain,(
    ! [A_91,B_92,C_93] : k3_xboole_0(k3_xboole_0(A_91,B_92),C_93) = k3_xboole_0(A_91,k3_xboole_0(B_92,C_93)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_944,plain,(
    ! [C_93] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_5',C_93)) = k3_xboole_0('#skF_4',C_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_861])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_38,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k4_xboole_0(A_24,B_25)) = k3_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_242,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k3_xboole_0(A_59,B_60)) = k4_xboole_0(A_59,B_60) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_248,plain,(
    ! [A_59,B_60] : k4_xboole_0(A_59,k4_xboole_0(A_59,B_60)) = k3_xboole_0(A_59,k3_xboole_0(A_59,B_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_242,c_38])).

tff(c_547,plain,(
    ! [A_81,B_82] : k3_xboole_0(A_81,k3_xboole_0(A_81,B_82)) = k3_xboole_0(A_81,B_82) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_248])).

tff(c_589,plain,(
    ! [A_1,B_2] : k3_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k3_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_547])).

tff(c_7565,plain,(
    ! [C_230,A_231,B_232] : k3_xboole_0(C_230,k3_xboole_0(A_231,B_232)) = k3_xboole_0(A_231,k3_xboole_0(B_232,C_230)) ),
    inference(superposition,[status(thm),theory(equality)],[c_861,c_2])).

tff(c_8328,plain,(
    ! [C_233] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_5',C_233)) = k3_xboole_0(C_233,'#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_157,c_7565])).

tff(c_8470,plain,(
    ! [B_2] : k3_xboole_0(k3_xboole_0(B_2,'#skF_5'),'#skF_4') = k3_xboole_0('#skF_4',k3_xboole_0('#skF_5',B_2)) ),
    inference(superposition,[status(thm),theory(equality)],[c_589,c_8328])).

tff(c_9833,plain,(
    ! [B_242] : k3_xboole_0(k3_xboole_0(B_242,'#skF_5'),'#skF_4') = k3_xboole_0('#skF_4',B_242) ),
    inference(demodulation,[status(thm),theory(equality)],[c_944,c_8470])).

tff(c_9966,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),'#skF_4') = k3_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_94,c_9833])).

tff(c_16023,plain,
    ( k3_xboole_0('#skF_4','#skF_6') = k1_tarski('#skF_7')
    | ~ r2_hidden('#skF_7','#skF_4')
    | ~ r2_hidden('#skF_7','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_15961,c_9966])).

tff(c_16280,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_52,c_16023])).

tff(c_16282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_50,c_16280])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:43:06 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 9.66/3.75  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.80/3.77  
% 9.80/3.77  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.80/3.77  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 9.80/3.77  
% 9.80/3.77  %Foreground sorts:
% 9.80/3.77  
% 9.80/3.77  
% 9.80/3.77  %Background operators:
% 9.80/3.77  
% 9.80/3.77  
% 9.80/3.77  %Foreground operators:
% 9.80/3.77  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 9.80/3.77  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 9.80/3.77  tff(k1_tarski, type, k1_tarski: $i > $i).
% 9.80/3.77  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 9.80/3.77  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 9.80/3.77  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 9.80/3.77  tff('#skF_7', type, '#skF_7': $i).
% 9.80/3.77  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 9.80/3.77  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 9.80/3.77  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 9.80/3.77  tff('#skF_5', type, '#skF_5': $i).
% 9.80/3.77  tff('#skF_6', type, '#skF_6': $i).
% 9.80/3.77  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 9.80/3.77  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 9.80/3.77  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 9.80/3.77  tff('#skF_4', type, '#skF_4': $i).
% 9.80/3.77  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 9.80/3.77  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 9.80/3.77  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 9.80/3.77  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 9.80/3.77  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 9.80/3.77  
% 9.80/3.78  tff(f_81, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 9.80/3.78  tff(f_60, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 9.80/3.78  tff(f_72, axiom, (![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k3_xboole_0(k2_tarski(A, C), B) = k2_tarski(A, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 9.80/3.78  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 9.80/3.78  tff(f_48, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 9.80/3.78  tff(f_52, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 9.80/3.78  tff(f_50, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t16_xboole_1)).
% 9.80/3.78  tff(f_58, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 9.80/3.78  tff(f_56, axiom, (![A, B]: (k4_xboole_0(A, k3_xboole_0(A, B)) = k4_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t47_xboole_1)).
% 9.80/3.78  tff(c_50, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.80/3.78  tff(c_52, plain, (r2_hidden('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.80/3.78  tff(c_40, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_60])).
% 9.80/3.78  tff(c_1758, plain, (![A_122, C_123, B_124]: (k3_xboole_0(k2_tarski(A_122, C_123), B_124)=k2_tarski(A_122, C_123) | ~r2_hidden(C_123, B_124) | ~r2_hidden(A_122, B_124))), inference(cnfTransformation, [status(thm)], [f_72])).
% 9.80/3.78  tff(c_1845, plain, (![A_26, B_124]: (k3_xboole_0(k1_tarski(A_26), B_124)=k2_tarski(A_26, A_26) | ~r2_hidden(A_26, B_124) | ~r2_hidden(A_26, B_124))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1758])).
% 9.80/3.78  tff(c_15961, plain, (![A_296, B_297]: (k3_xboole_0(k1_tarski(A_296), B_297)=k1_tarski(A_296) | ~r2_hidden(A_296, B_297) | ~r2_hidden(A_296, B_297))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1845])).
% 9.80/3.78  tff(c_79, plain, (![B_41, A_42]: (k3_xboole_0(B_41, A_42)=k3_xboole_0(A_42, B_41))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.80/3.78  tff(c_54, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.80/3.78  tff(c_94, plain, (k3_xboole_0('#skF_6', '#skF_5')=k1_tarski('#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_79, c_54])).
% 9.80/3.78  tff(c_56, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_81])).
% 9.80/3.78  tff(c_149, plain, (![A_47, B_48]: (k2_xboole_0(A_47, B_48)=B_48 | ~r1_tarski(A_47, B_48))), inference(cnfTransformation, [status(thm)], [f_48])).
% 9.80/3.78  tff(c_153, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_56, c_149])).
% 9.80/3.78  tff(c_32, plain, (![A_19, B_20]: (k3_xboole_0(A_19, k2_xboole_0(A_19, B_20))=A_19)), inference(cnfTransformation, [status(thm)], [f_52])).
% 9.80/3.78  tff(c_157, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_153, c_32])).
% 9.80/3.78  tff(c_861, plain, (![A_91, B_92, C_93]: (k3_xboole_0(k3_xboole_0(A_91, B_92), C_93)=k3_xboole_0(A_91, k3_xboole_0(B_92, C_93)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 9.80/3.78  tff(c_944, plain, (![C_93]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_5', C_93))=k3_xboole_0('#skF_4', C_93))), inference(superposition, [status(thm), theory('equality')], [c_157, c_861])).
% 9.80/3.78  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 9.80/3.78  tff(c_38, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k4_xboole_0(A_24, B_25))=k3_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_58])).
% 9.80/3.78  tff(c_242, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k3_xboole_0(A_59, B_60))=k4_xboole_0(A_59, B_60))), inference(cnfTransformation, [status(thm)], [f_56])).
% 9.80/3.78  tff(c_248, plain, (![A_59, B_60]: (k4_xboole_0(A_59, k4_xboole_0(A_59, B_60))=k3_xboole_0(A_59, k3_xboole_0(A_59, B_60)))), inference(superposition, [status(thm), theory('equality')], [c_242, c_38])).
% 9.80/3.78  tff(c_547, plain, (![A_81, B_82]: (k3_xboole_0(A_81, k3_xboole_0(A_81, B_82))=k3_xboole_0(A_81, B_82))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_248])).
% 9.80/3.78  tff(c_589, plain, (![A_1, B_2]: (k3_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k3_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_547])).
% 9.80/3.78  tff(c_7565, plain, (![C_230, A_231, B_232]: (k3_xboole_0(C_230, k3_xboole_0(A_231, B_232))=k3_xboole_0(A_231, k3_xboole_0(B_232, C_230)))), inference(superposition, [status(thm), theory('equality')], [c_861, c_2])).
% 9.80/3.78  tff(c_8328, plain, (![C_233]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_5', C_233))=k3_xboole_0(C_233, '#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_157, c_7565])).
% 9.80/3.78  tff(c_8470, plain, (![B_2]: (k3_xboole_0(k3_xboole_0(B_2, '#skF_5'), '#skF_4')=k3_xboole_0('#skF_4', k3_xboole_0('#skF_5', B_2)))), inference(superposition, [status(thm), theory('equality')], [c_589, c_8328])).
% 9.80/3.78  tff(c_9833, plain, (![B_242]: (k3_xboole_0(k3_xboole_0(B_242, '#skF_5'), '#skF_4')=k3_xboole_0('#skF_4', B_242))), inference(demodulation, [status(thm), theory('equality')], [c_944, c_8470])).
% 9.80/3.78  tff(c_9966, plain, (k3_xboole_0(k1_tarski('#skF_7'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_94, c_9833])).
% 9.80/3.78  tff(c_16023, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_tarski('#skF_7') | ~r2_hidden('#skF_7', '#skF_4') | ~r2_hidden('#skF_7', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_15961, c_9966])).
% 9.80/3.78  tff(c_16280, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_52, c_52, c_16023])).
% 9.80/3.78  tff(c_16282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_50, c_16280])).
% 9.80/3.78  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 9.80/3.78  
% 9.80/3.78  Inference rules
% 9.80/3.78  ----------------------
% 9.80/3.78  #Ref     : 0
% 9.80/3.78  #Sup     : 4051
% 9.80/3.78  #Fact    : 0
% 9.80/3.78  #Define  : 0
% 9.80/3.78  #Split   : 7
% 9.80/3.78  #Chain   : 0
% 9.80/3.78  #Close   : 0
% 9.80/3.78  
% 9.80/3.78  Ordering : KBO
% 9.80/3.78  
% 9.80/3.78  Simplification rules
% 9.80/3.78  ----------------------
% 9.80/3.78  #Subsume      : 580
% 9.80/3.78  #Demod        : 3768
% 9.80/3.78  #Tautology    : 2111
% 9.80/3.78  #SimpNegUnit  : 7
% 9.80/3.78  #BackRed      : 7
% 9.80/3.78  
% 9.80/3.78  #Partial instantiations: 0
% 9.80/3.78  #Strategies tried      : 1
% 9.80/3.78  
% 9.80/3.78  Timing (in seconds)
% 9.80/3.78  ----------------------
% 9.86/3.78  Preprocessing        : 0.42
% 9.86/3.78  Parsing              : 0.24
% 9.86/3.78  CNF conversion       : 0.02
% 9.86/3.78  Main loop            : 2.53
% 9.86/3.78  Inferencing          : 0.55
% 9.86/3.78  Reduction            : 1.40
% 9.86/3.78  Demodulation         : 1.21
% 9.86/3.78  BG Simplification    : 0.07
% 9.86/3.78  Subsumption          : 0.40
% 9.86/3.78  Abstraction          : 0.09
% 9.86/3.78  MUC search           : 0.00
% 9.86/3.78  Cooper               : 0.00
% 9.86/3.78  Total                : 2.99
% 9.86/3.78  Index Insertion      : 0.00
% 9.86/3.78  Index Deletion       : 0.00
% 9.86/3.78  Index Matching       : 0.00
% 9.86/3.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:57 EST 2020

% Result     : Theorem 12.39s
% Output     : CNFRefutation 12.39s
% Verified   : 
% Statistics : Number of formulae       :   57 (  70 expanded)
%              Number of leaves         :   32 (  40 expanded)
%              Depth                    :   10
%              Number of atoms          :   48 (  73 expanded)
%              Number of equality atoms :   31 (  47 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_65,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_83,axiom,(
    ! [A,B,C] :
      ( ( r2_hidden(A,B)
        & r2_hidden(C,B) )
     => k3_xboole_0(k2_tarski(A,C),B) = k2_tarski(A,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t53_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(c_54,plain,(
    k3_xboole_0('#skF_4','#skF_6') != k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_56,plain,(
    r2_hidden('#skF_7','#skF_4') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_38,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1518,plain,(
    ! [A_139,C_140,B_141] :
      ( k3_xboole_0(k2_tarski(A_139,C_140),B_141) = k2_tarski(A_139,C_140)
      | ~ r2_hidden(C_140,B_141)
      | ~ r2_hidden(A_139,B_141) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_1612,plain,(
    ! [A_27,B_141] :
      ( k3_xboole_0(k1_tarski(A_27),B_141) = k2_tarski(A_27,A_27)
      | ~ r2_hidden(A_27,B_141)
      | ~ r2_hidden(A_27,B_141) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1518])).

tff(c_30412,plain,(
    ! [A_488,B_489] :
      ( k3_xboole_0(k1_tarski(A_488),B_489) = k1_tarski(A_488)
      | ~ r2_hidden(A_488,B_489)
      | ~ r2_hidden(A_488,B_489) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_38,c_1612])).

tff(c_58,plain,(
    k3_xboole_0('#skF_5','#skF_6') = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_22,plain,(
    ! [A_9] : k3_xboole_0(A_9,A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_552,plain,(
    ! [A_99,B_100,C_101] : k3_xboole_0(k3_xboole_0(A_99,B_100),C_101) = k3_xboole_0(A_99,k3_xboole_0(B_100,C_101)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_632,plain,(
    ! [A_9,C_101] : k3_xboole_0(A_9,k3_xboole_0(A_9,C_101)) = k3_xboole_0(A_9,C_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_552])).

tff(c_60,plain,(
    r1_tarski('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_155,plain,(
    ! [A_69,B_70] :
      ( k2_xboole_0(A_69,B_70) = B_70
      | ~ r1_tarski(A_69,B_70) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_163,plain,(
    k2_xboole_0('#skF_4','#skF_5') = '#skF_5' ),
    inference(resolution,[status(thm)],[c_60,c_155])).

tff(c_32,plain,(
    ! [A_21,B_22] : k3_xboole_0(A_21,k2_xboole_0(A_21,B_22)) = A_21 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_167,plain,(
    k3_xboole_0('#skF_4','#skF_5') = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_163,c_32])).

tff(c_602,plain,(
    ! [C_101] : k3_xboole_0('#skF_4',k3_xboole_0('#skF_5',C_101)) = k3_xboole_0('#skF_4',C_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_552])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_14381,plain,(
    ! [A_379,A_377,B_378] : k3_xboole_0(A_379,k3_xboole_0(A_377,B_378)) = k3_xboole_0(A_377,k3_xboole_0(B_378,A_379)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_552])).

tff(c_15208,plain,(
    ! [A_381,A_382] : k3_xboole_0(A_381,k3_xboole_0(A_381,A_382)) = k3_xboole_0(A_382,A_381) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_14381])).

tff(c_15440,plain,(
    ! [C_101] : k3_xboole_0(k3_xboole_0('#skF_5',C_101),'#skF_4') = k3_xboole_0('#skF_4',k3_xboole_0('#skF_4',C_101)) ),
    inference(superposition,[status(thm),theory(equality)],[c_602,c_15208])).

tff(c_22411,plain,(
    ! [C_437] : k3_xboole_0(k3_xboole_0('#skF_5',C_437),'#skF_4') = k3_xboole_0('#skF_4',C_437) ),
    inference(demodulation,[status(thm),theory(equality)],[c_632,c_15440])).

tff(c_22642,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),'#skF_4') = k3_xboole_0('#skF_4','#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_22411])).

tff(c_30475,plain,
    ( k3_xboole_0('#skF_4','#skF_6') = k1_tarski('#skF_7')
    | ~ r2_hidden('#skF_7','#skF_4')
    | ~ r2_hidden('#skF_7','#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_30412,c_22642])).

tff(c_30890,plain,(
    k3_xboole_0('#skF_4','#skF_6') = k1_tarski('#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_56,c_30475])).

tff(c_30892,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_54,c_30890])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.11  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n014.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.33  % CPULimit   : 60
% 0.12/0.33  % DateTime   : Tue Dec  1 10:38:07 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.18/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.39/5.26  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.39/5.26  
% 12.39/5.26  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.39/5.27  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_1 > #skF_7 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 12.39/5.27  
% 12.39/5.27  %Foreground sorts:
% 12.39/5.27  
% 12.39/5.27  
% 12.39/5.27  %Background operators:
% 12.39/5.27  
% 12.39/5.27  
% 12.39/5.27  %Foreground operators:
% 12.39/5.27  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 12.39/5.27  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.39/5.27  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.39/5.27  tff(k1_tarski, type, k1_tarski: $i > $i).
% 12.39/5.27  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.39/5.27  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.39/5.27  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.39/5.27  tff('#skF_7', type, '#skF_7': $i).
% 12.39/5.27  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 12.39/5.27  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.39/5.27  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.39/5.27  tff('#skF_5', type, '#skF_5': $i).
% 12.39/5.27  tff('#skF_6', type, '#skF_6': $i).
% 12.39/5.27  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.39/5.27  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 12.39/5.27  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.39/5.27  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.39/5.27  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.39/5.27  tff('#skF_4', type, '#skF_4': $i).
% 12.39/5.27  tff('#skF_3', type, '#skF_3': $i > $i).
% 12.39/5.27  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.39/5.27  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.39/5.27  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.39/5.27  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.39/5.27  
% 12.39/5.28  tff(f_92, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 12.39/5.28  tff(f_65, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 12.39/5.28  tff(f_83, axiom, (![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k3_xboole_0(k2_tarski(A, C), B) = k2_tarski(A, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t53_zfmisc_1)).
% 12.39/5.28  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 12.39/5.28  tff(f_57, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 12.39/5.28  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 12.39/5.28  tff(f_59, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t21_xboole_1)).
% 12.39/5.28  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 12.39/5.28  tff(c_54, plain, (k3_xboole_0('#skF_4', '#skF_6')!=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.39/5.28  tff(c_56, plain, (r2_hidden('#skF_7', '#skF_4')), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.39/5.28  tff(c_38, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_65])).
% 12.39/5.28  tff(c_1518, plain, (![A_139, C_140, B_141]: (k3_xboole_0(k2_tarski(A_139, C_140), B_141)=k2_tarski(A_139, C_140) | ~r2_hidden(C_140, B_141) | ~r2_hidden(A_139, B_141))), inference(cnfTransformation, [status(thm)], [f_83])).
% 12.39/5.28  tff(c_1612, plain, (![A_27, B_141]: (k3_xboole_0(k1_tarski(A_27), B_141)=k2_tarski(A_27, A_27) | ~r2_hidden(A_27, B_141) | ~r2_hidden(A_27, B_141))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1518])).
% 12.39/5.28  tff(c_30412, plain, (![A_488, B_489]: (k3_xboole_0(k1_tarski(A_488), B_489)=k1_tarski(A_488) | ~r2_hidden(A_488, B_489) | ~r2_hidden(A_488, B_489))), inference(demodulation, [status(thm), theory('equality')], [c_38, c_1612])).
% 12.39/5.28  tff(c_58, plain, (k3_xboole_0('#skF_5', '#skF_6')=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.39/5.28  tff(c_22, plain, (![A_9]: (k3_xboole_0(A_9, A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.39/5.28  tff(c_552, plain, (![A_99, B_100, C_101]: (k3_xboole_0(k3_xboole_0(A_99, B_100), C_101)=k3_xboole_0(A_99, k3_xboole_0(B_100, C_101)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 12.39/5.28  tff(c_632, plain, (![A_9, C_101]: (k3_xboole_0(A_9, k3_xboole_0(A_9, C_101))=k3_xboole_0(A_9, C_101))), inference(superposition, [status(thm), theory('equality')], [c_22, c_552])).
% 12.39/5.28  tff(c_60, plain, (r1_tarski('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_92])).
% 12.39/5.28  tff(c_155, plain, (![A_69, B_70]: (k2_xboole_0(A_69, B_70)=B_70 | ~r1_tarski(A_69, B_70))), inference(cnfTransformation, [status(thm)], [f_55])).
% 12.39/5.28  tff(c_163, plain, (k2_xboole_0('#skF_4', '#skF_5')='#skF_5'), inference(resolution, [status(thm)], [c_60, c_155])).
% 12.39/5.28  tff(c_32, plain, (![A_21, B_22]: (k3_xboole_0(A_21, k2_xboole_0(A_21, B_22))=A_21)), inference(cnfTransformation, [status(thm)], [f_59])).
% 12.39/5.28  tff(c_167, plain, (k3_xboole_0('#skF_4', '#skF_5')='#skF_4'), inference(superposition, [status(thm), theory('equality')], [c_163, c_32])).
% 12.39/5.28  tff(c_602, plain, (![C_101]: (k3_xboole_0('#skF_4', k3_xboole_0('#skF_5', C_101))=k3_xboole_0('#skF_4', C_101))), inference(superposition, [status(thm), theory('equality')], [c_167, c_552])).
% 12.39/5.28  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.39/5.28  tff(c_14381, plain, (![A_379, A_377, B_378]: (k3_xboole_0(A_379, k3_xboole_0(A_377, B_378))=k3_xboole_0(A_377, k3_xboole_0(B_378, A_379)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_552])).
% 12.39/5.28  tff(c_15208, plain, (![A_381, A_382]: (k3_xboole_0(A_381, k3_xboole_0(A_381, A_382))=k3_xboole_0(A_382, A_381))), inference(superposition, [status(thm), theory('equality')], [c_22, c_14381])).
% 12.39/5.28  tff(c_15440, plain, (![C_101]: (k3_xboole_0(k3_xboole_0('#skF_5', C_101), '#skF_4')=k3_xboole_0('#skF_4', k3_xboole_0('#skF_4', C_101)))), inference(superposition, [status(thm), theory('equality')], [c_602, c_15208])).
% 12.39/5.28  tff(c_22411, plain, (![C_437]: (k3_xboole_0(k3_xboole_0('#skF_5', C_437), '#skF_4')=k3_xboole_0('#skF_4', C_437))), inference(demodulation, [status(thm), theory('equality')], [c_632, c_15440])).
% 12.39/5.28  tff(c_22642, plain, (k3_xboole_0(k1_tarski('#skF_7'), '#skF_4')=k3_xboole_0('#skF_4', '#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_58, c_22411])).
% 12.39/5.28  tff(c_30475, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_tarski('#skF_7') | ~r2_hidden('#skF_7', '#skF_4') | ~r2_hidden('#skF_7', '#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_30412, c_22642])).
% 12.39/5.28  tff(c_30890, plain, (k3_xboole_0('#skF_4', '#skF_6')=k1_tarski('#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_56, c_56, c_30475])).
% 12.39/5.28  tff(c_30892, plain, $false, inference(negUnitSimplification, [status(thm)], [c_54, c_30890])).
% 12.39/5.28  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 12.39/5.28  
% 12.39/5.28  Inference rules
% 12.39/5.28  ----------------------
% 12.39/5.28  #Ref     : 0
% 12.39/5.28  #Sup     : 7631
% 12.39/5.28  #Fact    : 0
% 12.39/5.28  #Define  : 0
% 12.39/5.28  #Split   : 1
% 12.39/5.28  #Chain   : 0
% 12.39/5.28  #Close   : 0
% 12.39/5.28  
% 12.39/5.28  Ordering : KBO
% 12.39/5.28  
% 12.39/5.28  Simplification rules
% 12.39/5.28  ----------------------
% 12.39/5.28  #Subsume      : 333
% 12.39/5.28  #Demod        : 7077
% 12.39/5.28  #Tautology    : 4200
% 12.39/5.28  #SimpNegUnit  : 5
% 12.39/5.28  #BackRed      : 66
% 12.39/5.28  
% 12.39/5.28  #Partial instantiations: 0
% 12.39/5.28  #Strategies tried      : 1
% 12.39/5.28  
% 12.39/5.28  Timing (in seconds)
% 12.39/5.28  ----------------------
% 12.39/5.28  Preprocessing        : 0.33
% 12.39/5.28  Parsing              : 0.17
% 12.39/5.28  CNF conversion       : 0.02
% 12.39/5.28  Main loop            : 4.21
% 12.39/5.28  Inferencing          : 0.74
% 12.39/5.28  Reduction            : 2.47
% 12.39/5.28  Demodulation         : 2.21
% 12.39/5.28  BG Simplification    : 0.10
% 12.39/5.28  Subsumption          : 0.69
% 12.39/5.28  Abstraction          : 0.12
% 12.39/5.28  MUC search           : 0.00
% 12.39/5.28  Cooper               : 0.00
% 12.39/5.28  Total                : 4.56
% 12.39/5.28  Index Insertion      : 0.00
% 12.39/5.28  Index Deletion       : 0.00
% 12.39/5.28  Index Matching       : 0.00
% 12.39/5.28  BG Taut test         : 0.00
%------------------------------------------------------------------------------

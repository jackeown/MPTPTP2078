%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:56 EST 2020

% Result     : Theorem 5.80s
% Output     : CNFRefutation 5.80s
% Verified   : 
% Statistics : Number of formulae       :   47 (  57 expanded)
%              Number of leaves         :   25 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   53 (  77 expanded)
%              Number of equality atoms :   25 (  38 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4

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

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_75,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ( ( r1_tarski(A,B)
          & k3_xboole_0(B,C) = k1_tarski(D)
          & r2_hidden(D,A) )
       => k3_xboole_0(A,C) = k1_tarski(D) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t148_zfmisc_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_48,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & ! [D] :
            ( ( r1_tarski(D,B)
              & r1_tarski(D,C) )
           => r1_tarski(D,A) ) )
     => A = k3_xboole_0(B,C) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t20_xboole_1)).

tff(f_35,axiom,(
    ! [A,B,C] : k3_xboole_0(k3_xboole_0(A,B),C) = k3_xboole_0(A,k3_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t16_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_34,plain,(
    k3_xboole_0('#skF_2','#skF_4') != k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_42,plain,(
    k3_xboole_0('#skF_4','#skF_2') != k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_34])).

tff(c_36,plain,(
    r2_hidden('#skF_5','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_40,plain,(
    r1_tarski('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_8,plain,(
    ! [B_4] : r1_tarski(B_4,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_16,plain,(
    ! [A_8,B_9,C_10] :
      ( r1_tarski('#skF_1'(A_8,B_9,C_10),B_9)
      | k3_xboole_0(B_9,C_10) = A_8
      | ~ r1_tarski(A_8,C_10)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3769,plain,(
    ! [A_112,B_113,C_114] :
      ( ~ r1_tarski('#skF_1'(A_112,B_113,C_114),A_112)
      | k3_xboole_0(B_113,C_114) = A_112
      | ~ r1_tarski(A_112,C_114)
      | ~ r1_tarski(A_112,B_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_3773,plain,(
    ! [B_9,C_10] :
      ( k3_xboole_0(B_9,C_10) = B_9
      | ~ r1_tarski(B_9,C_10)
      | ~ r1_tarski(B_9,B_9) ) ),
    inference(resolution,[status(thm)],[c_16,c_3769])).

tff(c_3784,plain,(
    ! [B_115,C_116] :
      ( k3_xboole_0(B_115,C_116) = B_115
      | ~ r1_tarski(B_115,C_116) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_3773])).

tff(c_3802,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(resolution,[status(thm)],[c_40,c_3784])).

tff(c_192,plain,(
    ! [A_57,B_58,C_59] : k3_xboole_0(k3_xboole_0(A_57,B_58),C_59) = k3_xboole_0(A_57,k3_xboole_0(B_58,C_59)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_205,plain,(
    ! [C_59,A_57,B_58] : k3_xboole_0(C_59,k3_xboole_0(A_57,B_58)) = k3_xboole_0(A_57,k3_xboole_0(B_58,C_59)) ),
    inference(superposition,[status(thm),theory(equality)],[c_192,c_2])).

tff(c_38,plain,(
    k3_xboole_0('#skF_3','#skF_4') = k1_tarski('#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_249,plain,(
    ! [C_60] : k3_xboole_0(k1_tarski('#skF_5'),C_60) = k3_xboole_0('#skF_3',k3_xboole_0('#skF_4',C_60)) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_192])).

tff(c_129,plain,(
    ! [B_50,A_51] :
      ( k3_xboole_0(B_50,k1_tarski(A_51)) = k1_tarski(A_51)
      | ~ r2_hidden(A_51,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_135,plain,(
    ! [A_51,B_50] :
      ( k3_xboole_0(k1_tarski(A_51),B_50) = k1_tarski(A_51)
      | ~ r2_hidden(A_51,B_50) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_2])).

tff(c_258,plain,(
    ! [C_60] :
      ( k3_xboole_0('#skF_3',k3_xboole_0('#skF_4',C_60)) = k1_tarski('#skF_5')
      | ~ r2_hidden('#skF_5',C_60) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_135])).

tff(c_893,plain,(
    ! [C_60] :
      ( k3_xboole_0('#skF_4',k3_xboole_0(C_60,'#skF_3')) = k1_tarski('#skF_5')
      | ~ r2_hidden('#skF_5',C_60) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_205,c_258])).

tff(c_4042,plain,
    ( k3_xboole_0('#skF_4','#skF_2') = k1_tarski('#skF_5')
    | ~ r2_hidden('#skF_5','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_3802,c_893])).

tff(c_4085,plain,(
    k3_xboole_0('#skF_4','#skF_2') = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_4042])).

tff(c_4087,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_42,c_4085])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:32:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.80/2.22  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.80/2.22  
% 5.80/2.22  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.80/2.22  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_tarski > #nlpp > k1_tarski > #skF_1 > #skF_5 > #skF_2 > #skF_3 > #skF_4
% 5.80/2.22  
% 5.80/2.22  %Foreground sorts:
% 5.80/2.22  
% 5.80/2.22  
% 5.80/2.22  %Background operators:
% 5.80/2.22  
% 5.80/2.22  
% 5.80/2.22  %Foreground operators:
% 5.80/2.22  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 5.80/2.22  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.80/2.22  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.80/2.22  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.80/2.22  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.80/2.22  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.80/2.22  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.80/2.22  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.80/2.22  tff('#skF_5', type, '#skF_5': $i).
% 5.80/2.22  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.80/2.22  tff('#skF_2', type, '#skF_2': $i).
% 5.80/2.22  tff('#skF_3', type, '#skF_3': $i).
% 5.80/2.22  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.80/2.22  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.80/2.22  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.80/2.22  tff('#skF_4', type, '#skF_4': $i).
% 5.80/2.22  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.80/2.22  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.80/2.22  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.80/2.22  
% 5.80/2.23  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 5.80/2.23  tff(f_75, negated_conjecture, ~(![A, B, C, D]: (((r1_tarski(A, B) & (k3_xboole_0(B, C) = k1_tarski(D))) & r2_hidden(D, A)) => (k3_xboole_0(A, C) = k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t148_zfmisc_1)).
% 5.80/2.23  tff(f_33, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 5.80/2.23  tff(f_48, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & (![D]: ((r1_tarski(D, B) & r1_tarski(D, C)) => r1_tarski(D, A)))) => (A = k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t20_xboole_1)).
% 5.80/2.23  tff(f_35, axiom, (![A, B, C]: (k3_xboole_0(k3_xboole_0(A, B), C) = k3_xboole_0(A, k3_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t16_xboole_1)).
% 5.80/2.23  tff(f_66, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 5.80/2.23  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.80/2.23  tff(c_34, plain, (k3_xboole_0('#skF_2', '#skF_4')!=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.80/2.23  tff(c_42, plain, (k3_xboole_0('#skF_4', '#skF_2')!=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_34])).
% 5.80/2.23  tff(c_36, plain, (r2_hidden('#skF_5', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.80/2.23  tff(c_40, plain, (r1_tarski('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.80/2.23  tff(c_8, plain, (![B_4]: (r1_tarski(B_4, B_4))), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.80/2.23  tff(c_16, plain, (![A_8, B_9, C_10]: (r1_tarski('#skF_1'(A_8, B_9, C_10), B_9) | k3_xboole_0(B_9, C_10)=A_8 | ~r1_tarski(A_8, C_10) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.80/2.23  tff(c_3769, plain, (![A_112, B_113, C_114]: (~r1_tarski('#skF_1'(A_112, B_113, C_114), A_112) | k3_xboole_0(B_113, C_114)=A_112 | ~r1_tarski(A_112, C_114) | ~r1_tarski(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_48])).
% 5.80/2.23  tff(c_3773, plain, (![B_9, C_10]: (k3_xboole_0(B_9, C_10)=B_9 | ~r1_tarski(B_9, C_10) | ~r1_tarski(B_9, B_9))), inference(resolution, [status(thm)], [c_16, c_3769])).
% 5.80/2.23  tff(c_3784, plain, (![B_115, C_116]: (k3_xboole_0(B_115, C_116)=B_115 | ~r1_tarski(B_115, C_116))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_3773])).
% 5.80/2.23  tff(c_3802, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(resolution, [status(thm)], [c_40, c_3784])).
% 5.80/2.23  tff(c_192, plain, (![A_57, B_58, C_59]: (k3_xboole_0(k3_xboole_0(A_57, B_58), C_59)=k3_xboole_0(A_57, k3_xboole_0(B_58, C_59)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.80/2.23  tff(c_205, plain, (![C_59, A_57, B_58]: (k3_xboole_0(C_59, k3_xboole_0(A_57, B_58))=k3_xboole_0(A_57, k3_xboole_0(B_58, C_59)))), inference(superposition, [status(thm), theory('equality')], [c_192, c_2])).
% 5.80/2.23  tff(c_38, plain, (k3_xboole_0('#skF_3', '#skF_4')=k1_tarski('#skF_5')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.80/2.23  tff(c_249, plain, (![C_60]: (k3_xboole_0(k1_tarski('#skF_5'), C_60)=k3_xboole_0('#skF_3', k3_xboole_0('#skF_4', C_60)))), inference(superposition, [status(thm), theory('equality')], [c_38, c_192])).
% 5.80/2.23  tff(c_129, plain, (![B_50, A_51]: (k3_xboole_0(B_50, k1_tarski(A_51))=k1_tarski(A_51) | ~r2_hidden(A_51, B_50))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.80/2.23  tff(c_135, plain, (![A_51, B_50]: (k3_xboole_0(k1_tarski(A_51), B_50)=k1_tarski(A_51) | ~r2_hidden(A_51, B_50))), inference(superposition, [status(thm), theory('equality')], [c_129, c_2])).
% 5.80/2.23  tff(c_258, plain, (![C_60]: (k3_xboole_0('#skF_3', k3_xboole_0('#skF_4', C_60))=k1_tarski('#skF_5') | ~r2_hidden('#skF_5', C_60))), inference(superposition, [status(thm), theory('equality')], [c_249, c_135])).
% 5.80/2.23  tff(c_893, plain, (![C_60]: (k3_xboole_0('#skF_4', k3_xboole_0(C_60, '#skF_3'))=k1_tarski('#skF_5') | ~r2_hidden('#skF_5', C_60))), inference(demodulation, [status(thm), theory('equality')], [c_205, c_258])).
% 5.80/2.23  tff(c_4042, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_tarski('#skF_5') | ~r2_hidden('#skF_5', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_3802, c_893])).
% 5.80/2.23  tff(c_4085, plain, (k3_xboole_0('#skF_4', '#skF_2')=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_36, c_4042])).
% 5.80/2.23  tff(c_4087, plain, $false, inference(negUnitSimplification, [status(thm)], [c_42, c_4085])).
% 5.80/2.23  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.80/2.23  
% 5.80/2.23  Inference rules
% 5.80/2.23  ----------------------
% 5.80/2.23  #Ref     : 0
% 5.80/2.23  #Sup     : 1049
% 5.80/2.23  #Fact    : 0
% 5.80/2.23  #Define  : 0
% 5.80/2.23  #Split   : 1
% 5.80/2.23  #Chain   : 0
% 5.80/2.23  #Close   : 0
% 5.80/2.23  
% 5.80/2.23  Ordering : KBO
% 5.80/2.23  
% 5.80/2.23  Simplification rules
% 5.80/2.23  ----------------------
% 5.80/2.23  #Subsume      : 184
% 5.80/2.23  #Demod        : 591
% 5.80/2.23  #Tautology    : 216
% 5.80/2.23  #SimpNegUnit  : 1
% 5.80/2.23  #BackRed      : 2
% 5.80/2.23  
% 5.80/2.23  #Partial instantiations: 0
% 5.80/2.23  #Strategies tried      : 1
% 5.80/2.23  
% 5.80/2.23  Timing (in seconds)
% 5.80/2.23  ----------------------
% 5.80/2.24  Preprocessing        : 0.34
% 5.80/2.24  Parsing              : 0.18
% 5.80/2.24  CNF conversion       : 0.02
% 5.80/2.24  Main loop            : 1.08
% 5.80/2.24  Inferencing          : 0.25
% 5.80/2.24  Reduction            : 0.63
% 5.80/2.24  Demodulation         : 0.56
% 5.80/2.24  BG Simplification    : 0.05
% 5.80/2.24  Subsumption          : 0.13
% 5.80/2.24  Abstraction          : 0.05
% 5.80/2.24  MUC search           : 0.00
% 5.80/2.24  Cooper               : 0.00
% 5.80/2.24  Total                : 1.44
% 5.80/2.24  Index Insertion      : 0.00
% 5.80/2.24  Index Deletion       : 0.00
% 5.80/2.24  Index Matching       : 0.00
% 5.80/2.24  BG Taut test         : 0.00
%------------------------------------------------------------------------------

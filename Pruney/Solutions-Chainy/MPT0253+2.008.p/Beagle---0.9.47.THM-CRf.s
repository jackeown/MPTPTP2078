%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:15 EST 2020

% Result     : Theorem 10.97s
% Output     : CNFRefutation 10.97s
% Verified   : 
% Statistics : Number of formulae       :   47 (  58 expanded)
%              Number of leaves         :   26 (  32 expanded)
%              Depth                    :    7
%              Number of atoms          :   46 (  61 expanded)
%              Number of equality atoms :   23 (  34 expanded)
%              Maximal formula depth    :    7 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff('#skF_1',type,(
    '#skF_1': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ( ( r2_hidden(A,B)
          & r2_hidden(C,B) )
       => k2_xboole_0(k2_tarski(A,C),B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_zfmisc_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,k4_xboole_0(B,A)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(k3_xboole_0(A,B),k4_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t51_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_59,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(c_44,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_42,plain,(
    r2_hidden('#skF_3','#skF_2') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_16,plain,(
    ! [A_10,B_11] : k2_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1143,plain,(
    ! [A_111,B_112,C_113] :
      ( r1_tarski(k2_tarski(A_111,B_112),C_113)
      | ~ r2_hidden(B_112,C_113)
      | ~ r2_hidden(A_111,C_113) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_14,plain,(
    ! [A_8,B_9] :
      ( k3_xboole_0(A_8,B_9) = A_8
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_4286,plain,(
    ! [A_178,B_179,C_180] :
      ( k3_xboole_0(k2_tarski(A_178,B_179),C_180) = k2_tarski(A_178,B_179)
      | ~ r2_hidden(B_179,C_180)
      | ~ r2_hidden(A_178,C_180) ) ),
    inference(resolution,[status(thm)],[c_1143,c_14])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_482,plain,(
    ! [A_64,B_65] : k2_xboole_0(k3_xboole_0(A_64,B_65),k4_xboole_0(A_64,B_65)) = A_64 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_521,plain,(
    ! [A_1,B_2] : k2_xboole_0(k3_xboole_0(A_1,B_2),k4_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_482])).

tff(c_4342,plain,(
    ! [A_178,B_179,C_180] :
      ( k2_xboole_0(k2_tarski(A_178,B_179),k4_xboole_0(C_180,k2_tarski(A_178,B_179))) = C_180
      | ~ r2_hidden(B_179,C_180)
      | ~ r2_hidden(A_178,C_180) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4286,c_521])).

tff(c_12190,plain,(
    ! [A_262,B_263,C_264] :
      ( k2_xboole_0(k2_tarski(A_262,B_263),C_264) = C_264
      | ~ r2_hidden(B_263,C_264)
      | ~ r2_hidden(A_262,C_264) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_4342])).

tff(c_24,plain,(
    ! [B_19,A_18] : k2_tarski(B_19,A_18) = k2_tarski(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_167,plain,(
    ! [A_49,B_50] : k3_tarski(k2_tarski(A_49,B_50)) = k2_xboole_0(A_49,B_50) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_182,plain,(
    ! [B_51,A_52] : k3_tarski(k2_tarski(B_51,A_52)) = k2_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_167])).

tff(c_32,plain,(
    ! [A_29,B_30] : k3_tarski(k2_tarski(A_29,B_30)) = k2_xboole_0(A_29,B_30) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_188,plain,(
    ! [B_51,A_52] : k2_xboole_0(B_51,A_52) = k2_xboole_0(A_52,B_51) ),
    inference(superposition,[status(thm),theory(equality)],[c_182,c_32])).

tff(c_28895,plain,(
    ! [C_364,A_365,B_366] :
      ( k2_xboole_0(C_364,k2_tarski(A_365,B_366)) = C_364
      | ~ r2_hidden(B_366,C_364)
      | ~ r2_hidden(A_365,C_364) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12190,c_188])).

tff(c_40,plain,(
    k2_xboole_0(k2_tarski('#skF_1','#skF_3'),'#skF_2') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_205,plain,(
    k2_xboole_0('#skF_2',k2_tarski('#skF_1','#skF_3')) != '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_188,c_40])).

tff(c_29126,plain,
    ( ~ r2_hidden('#skF_3','#skF_2')
    | ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_28895,c_205])).

tff(c_29270,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_42,c_29126])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n021.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:20:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.97/5.29  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.97/5.30  
% 10.97/5.30  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.97/5.30  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 10.97/5.30  
% 10.97/5.30  %Foreground sorts:
% 10.97/5.30  
% 10.97/5.30  
% 10.97/5.30  %Background operators:
% 10.97/5.30  
% 10.97/5.30  
% 10.97/5.30  %Foreground operators:
% 10.97/5.30  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.97/5.30  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 10.97/5.30  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 10.97/5.30  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 10.97/5.30  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.97/5.30  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 10.97/5.30  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.97/5.30  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.97/5.30  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.97/5.30  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.97/5.30  tff('#skF_2', type, '#skF_2': $i).
% 10.97/5.30  tff('#skF_3', type, '#skF_3': $i).
% 10.97/5.30  tff('#skF_1', type, '#skF_1': $i).
% 10.97/5.30  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.97/5.30  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.97/5.30  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.97/5.30  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 10.97/5.30  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.97/5.30  
% 10.97/5.31  tff(f_72, negated_conjecture, ~(![A, B, C]: ((r2_hidden(A, B) & r2_hidden(C, B)) => (k2_xboole_0(k2_tarski(A, C), B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_zfmisc_1)).
% 10.97/5.31  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, k4_xboole_0(B, A)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_xboole_1)).
% 10.97/5.31  tff(f_65, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 10.97/5.31  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 10.97/5.31  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 10.97/5.31  tff(f_47, axiom, (![A, B]: (k2_xboole_0(k3_xboole_0(A, B), k4_xboole_0(A, B)) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t51_xboole_1)).
% 10.97/5.31  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 10.97/5.31  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 10.97/5.31  tff(c_44, plain, (r2_hidden('#skF_1', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.97/5.31  tff(c_42, plain, (r2_hidden('#skF_3', '#skF_2')), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.97/5.31  tff(c_16, plain, (![A_10, B_11]: (k2_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_43])).
% 10.97/5.31  tff(c_1143, plain, (![A_111, B_112, C_113]: (r1_tarski(k2_tarski(A_111, B_112), C_113) | ~r2_hidden(B_112, C_113) | ~r2_hidden(A_111, C_113))), inference(cnfTransformation, [status(thm)], [f_65])).
% 10.97/5.31  tff(c_14, plain, (![A_8, B_9]: (k3_xboole_0(A_8, B_9)=A_8 | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_41])).
% 10.97/5.31  tff(c_4286, plain, (![A_178, B_179, C_180]: (k3_xboole_0(k2_tarski(A_178, B_179), C_180)=k2_tarski(A_178, B_179) | ~r2_hidden(B_179, C_180) | ~r2_hidden(A_178, C_180))), inference(resolution, [status(thm)], [c_1143, c_14])).
% 10.97/5.31  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.97/5.31  tff(c_482, plain, (![A_64, B_65]: (k2_xboole_0(k3_xboole_0(A_64, B_65), k4_xboole_0(A_64, B_65))=A_64)), inference(cnfTransformation, [status(thm)], [f_47])).
% 10.97/5.31  tff(c_521, plain, (![A_1, B_2]: (k2_xboole_0(k3_xboole_0(A_1, B_2), k4_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_482])).
% 10.97/5.31  tff(c_4342, plain, (![A_178, B_179, C_180]: (k2_xboole_0(k2_tarski(A_178, B_179), k4_xboole_0(C_180, k2_tarski(A_178, B_179)))=C_180 | ~r2_hidden(B_179, C_180) | ~r2_hidden(A_178, C_180))), inference(superposition, [status(thm), theory('equality')], [c_4286, c_521])).
% 10.97/5.31  tff(c_12190, plain, (![A_262, B_263, C_264]: (k2_xboole_0(k2_tarski(A_262, B_263), C_264)=C_264 | ~r2_hidden(B_263, C_264) | ~r2_hidden(A_262, C_264))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_4342])).
% 10.97/5.31  tff(c_24, plain, (![B_19, A_18]: (k2_tarski(B_19, A_18)=k2_tarski(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_51])).
% 10.97/5.31  tff(c_167, plain, (![A_49, B_50]: (k3_tarski(k2_tarski(A_49, B_50))=k2_xboole_0(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.97/5.31  tff(c_182, plain, (![B_51, A_52]: (k3_tarski(k2_tarski(B_51, A_52))=k2_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_24, c_167])).
% 10.97/5.31  tff(c_32, plain, (![A_29, B_30]: (k3_tarski(k2_tarski(A_29, B_30))=k2_xboole_0(A_29, B_30))), inference(cnfTransformation, [status(thm)], [f_59])).
% 10.97/5.31  tff(c_188, plain, (![B_51, A_52]: (k2_xboole_0(B_51, A_52)=k2_xboole_0(A_52, B_51))), inference(superposition, [status(thm), theory('equality')], [c_182, c_32])).
% 10.97/5.31  tff(c_28895, plain, (![C_364, A_365, B_366]: (k2_xboole_0(C_364, k2_tarski(A_365, B_366))=C_364 | ~r2_hidden(B_366, C_364) | ~r2_hidden(A_365, C_364))), inference(superposition, [status(thm), theory('equality')], [c_12190, c_188])).
% 10.97/5.31  tff(c_40, plain, (k2_xboole_0(k2_tarski('#skF_1', '#skF_3'), '#skF_2')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_72])).
% 10.97/5.31  tff(c_205, plain, (k2_xboole_0('#skF_2', k2_tarski('#skF_1', '#skF_3'))!='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_188, c_40])).
% 10.97/5.31  tff(c_29126, plain, (~r2_hidden('#skF_3', '#skF_2') | ~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_28895, c_205])).
% 10.97/5.31  tff(c_29270, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_44, c_42, c_29126])).
% 10.97/5.31  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 10.97/5.31  
% 10.97/5.31  Inference rules
% 10.97/5.31  ----------------------
% 10.97/5.31  #Ref     : 0
% 10.97/5.31  #Sup     : 7223
% 10.97/5.31  #Fact    : 0
% 10.97/5.31  #Define  : 0
% 10.97/5.31  #Split   : 0
% 10.97/5.31  #Chain   : 0
% 10.97/5.31  #Close   : 0
% 10.97/5.31  
% 10.97/5.31  Ordering : KBO
% 10.97/5.31  
% 10.97/5.31  Simplification rules
% 10.97/5.31  ----------------------
% 10.97/5.31  #Subsume      : 584
% 10.97/5.31  #Demod        : 15559
% 10.97/5.31  #Tautology    : 5391
% 10.97/5.31  #SimpNegUnit  : 0
% 10.97/5.31  #BackRed      : 13
% 10.97/5.31  
% 10.97/5.31  #Partial instantiations: 0
% 10.97/5.31  #Strategies tried      : 1
% 10.97/5.31  
% 10.97/5.31  Timing (in seconds)
% 10.97/5.31  ----------------------
% 10.97/5.31  Preprocessing        : 0.30
% 10.97/5.31  Parsing              : 0.16
% 10.97/5.31  CNF conversion       : 0.02
% 10.97/5.31  Main loop            : 4.25
% 10.97/5.31  Inferencing          : 0.74
% 10.97/5.31  Reduction            : 2.84
% 10.97/5.31  Demodulation         : 2.63
% 10.97/5.31  BG Simplification    : 0.07
% 10.97/5.31  Subsumption          : 0.46
% 10.97/5.31  Abstraction          : 0.20
% 10.97/5.31  MUC search           : 0.00
% 10.97/5.31  Cooper               : 0.00
% 10.97/5.31  Total                : 4.58
% 10.97/5.31  Index Insertion      : 0.00
% 10.97/5.31  Index Deletion       : 0.00
% 10.97/5.31  Index Matching       : 0.00
% 10.97/5.31  BG Taut test         : 0.00
%------------------------------------------------------------------------------

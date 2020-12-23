%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:42 EST 2020

% Result     : Theorem 10.08s
% Output     : CNFRefutation 10.08s
% Verified   : 
% Statistics : Number of formulae       :   50 (  77 expanded)
%              Number of leaves         :   23 (  37 expanded)
%              Depth                    :    6
%              Number of atoms          :   50 ( 106 expanded)
%              Number of equality atoms :   10 (  18 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff(k2_zfmisc_1,type,(
    k2_zfmisc_1: ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_64,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_57,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_26,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10483,plain,(
    ! [A_223,C_224,B_225] : k2_xboole_0(k2_zfmisc_1(A_223,C_224),k2_zfmisc_1(B_225,C_224)) = k2_zfmisc_1(k2_xboole_0(A_223,B_225),C_224) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_12934,plain,(
    ! [B_269,C_270,A_271] : k2_xboole_0(k2_zfmisc_1(B_269,C_270),k2_zfmisc_1(A_271,C_270)) = k2_zfmisc_1(k2_xboole_0(A_271,B_269),C_270) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10483])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_479,plain,(
    ! [A_52,C_53,B_54] :
      ( r1_tarski(A_52,C_53)
      | ~ r1_tarski(B_54,C_53)
      | ~ r1_tarski(A_52,B_54) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_501,plain,(
    ! [A_52,A_8,B_9] :
      ( r1_tarski(A_52,k2_xboole_0(A_8,B_9))
      | ~ r1_tarski(A_52,A_8) ) ),
    inference(resolution,[status(thm)],[c_8,c_479])).

tff(c_17154,plain,(
    ! [A_331,A_332,B_333,C_334] :
      ( r1_tarski(A_331,k2_zfmisc_1(k2_xboole_0(A_332,B_333),C_334))
      | ~ r1_tarski(A_331,k2_zfmisc_1(B_333,C_334)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_12934,c_501])).

tff(c_10805,plain,(
    ! [C_233,A_234,B_235] : k2_xboole_0(k2_zfmisc_1(C_233,A_234),k2_zfmisc_1(C_233,B_235)) = k2_zfmisc_1(C_233,k2_xboole_0(A_234,B_235)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_11774,plain,(
    ! [C_252,B_253,A_254] : k2_xboole_0(k2_zfmisc_1(C_252,B_253),k2_zfmisc_1(C_252,A_254)) = k2_zfmisc_1(C_252,k2_xboole_0(A_254,B_253)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_10805])).

tff(c_16693,plain,(
    ! [A_323,C_324,A_325,B_326] :
      ( r1_tarski(A_323,k2_zfmisc_1(C_324,k2_xboole_0(A_325,B_326)))
      | ~ r1_tarski(A_323,k2_zfmisc_1(C_324,B_326)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11774,c_501])).

tff(c_28,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_2013,plain,(
    ! [A_95,C_96,B_97] : k2_xboole_0(k2_zfmisc_1(A_95,C_96),k2_zfmisc_1(B_97,C_96)) = k2_zfmisc_1(k2_xboole_0(A_95,B_97),C_96) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_9102,plain,(
    ! [A_203,A_204,B_205,C_206] :
      ( r1_tarski(A_203,k2_zfmisc_1(k2_xboole_0(A_204,B_205),C_206))
      | ~ r1_tarski(A_203,k2_zfmisc_1(A_204,C_206)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2013,c_501])).

tff(c_1741,plain,(
    ! [C_84,A_85,B_86] : k2_xboole_0(k2_zfmisc_1(C_84,A_85),k2_zfmisc_1(C_84,B_86)) = k2_zfmisc_1(C_84,k2_xboole_0(A_85,B_86)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_7281,plain,(
    ! [A_177,C_178,A_179,B_180] :
      ( r1_tarski(A_177,k2_zfmisc_1(C_178,k2_xboole_0(A_179,B_180)))
      | ~ r1_tarski(A_177,k2_zfmisc_1(C_178,A_179)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1741,c_501])).

tff(c_697,plain,(
    ! [A_65,C_66,B_67] :
      ( r1_tarski(k2_xboole_0(A_65,C_66),B_67)
      | ~ r1_tarski(C_66,B_67)
      | ~ r1_tarski(A_65,B_67) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_24,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_734,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_697,c_24])).

tff(c_855,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_734])).

tff(c_7421,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_7281,c_855])).

tff(c_9114,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_9102,c_7421])).

tff(c_9257,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_28,c_9114])).

tff(c_9258,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_734])).

tff(c_16839,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_6')) ),
    inference(resolution,[status(thm)],[c_16693,c_9258])).

tff(c_17160,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(resolution,[status(thm)],[c_17154,c_16839])).

tff(c_17304,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_17160])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:30:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 10.08/3.92  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.08/3.93  
% 10.08/3.93  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.08/3.93  %$ r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 10.08/3.93  
% 10.08/3.93  %Foreground sorts:
% 10.08/3.93  
% 10.08/3.93  
% 10.08/3.93  %Background operators:
% 10.08/3.93  
% 10.08/3.93  
% 10.08/3.93  %Foreground operators:
% 10.08/3.93  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 10.08/3.93  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 10.08/3.93  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 10.08/3.93  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 10.08/3.93  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 10.08/3.93  tff('#skF_5', type, '#skF_5': $i).
% 10.08/3.93  tff('#skF_6', type, '#skF_6': $i).
% 10.08/3.93  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 10.08/3.93  tff('#skF_2', type, '#skF_2': $i).
% 10.08/3.93  tff('#skF_3', type, '#skF_3': $i).
% 10.08/3.93  tff('#skF_1', type, '#skF_1': $i).
% 10.08/3.93  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 10.08/3.93  tff(k3_tarski, type, k3_tarski: $i > $i).
% 10.08/3.93  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 10.08/3.93  tff('#skF_4', type, '#skF_4': $i).
% 10.08/3.93  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 10.08/3.93  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 10.08/3.93  
% 10.08/3.94  tff(f_64, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 10.08/3.94  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 10.08/3.94  tff(f_57, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 10.08/3.94  tff(f_39, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 10.08/3.94  tff(f_37, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 10.08/3.94  tff(f_45, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 10.08/3.94  tff(c_26, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.08/3.94  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 10.08/3.94  tff(c_10483, plain, (![A_223, C_224, B_225]: (k2_xboole_0(k2_zfmisc_1(A_223, C_224), k2_zfmisc_1(B_225, C_224))=k2_zfmisc_1(k2_xboole_0(A_223, B_225), C_224))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.08/3.94  tff(c_12934, plain, (![B_269, C_270, A_271]: (k2_xboole_0(k2_zfmisc_1(B_269, C_270), k2_zfmisc_1(A_271, C_270))=k2_zfmisc_1(k2_xboole_0(A_271, B_269), C_270))), inference(superposition, [status(thm), theory('equality')], [c_2, c_10483])).
% 10.08/3.94  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 10.08/3.94  tff(c_479, plain, (![A_52, C_53, B_54]: (r1_tarski(A_52, C_53) | ~r1_tarski(B_54, C_53) | ~r1_tarski(A_52, B_54))), inference(cnfTransformation, [status(thm)], [f_37])).
% 10.08/3.94  tff(c_501, plain, (![A_52, A_8, B_9]: (r1_tarski(A_52, k2_xboole_0(A_8, B_9)) | ~r1_tarski(A_52, A_8))), inference(resolution, [status(thm)], [c_8, c_479])).
% 10.08/3.94  tff(c_17154, plain, (![A_331, A_332, B_333, C_334]: (r1_tarski(A_331, k2_zfmisc_1(k2_xboole_0(A_332, B_333), C_334)) | ~r1_tarski(A_331, k2_zfmisc_1(B_333, C_334)))), inference(superposition, [status(thm), theory('equality')], [c_12934, c_501])).
% 10.08/3.94  tff(c_10805, plain, (![C_233, A_234, B_235]: (k2_xboole_0(k2_zfmisc_1(C_233, A_234), k2_zfmisc_1(C_233, B_235))=k2_zfmisc_1(C_233, k2_xboole_0(A_234, B_235)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.08/3.94  tff(c_11774, plain, (![C_252, B_253, A_254]: (k2_xboole_0(k2_zfmisc_1(C_252, B_253), k2_zfmisc_1(C_252, A_254))=k2_zfmisc_1(C_252, k2_xboole_0(A_254, B_253)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_10805])).
% 10.08/3.94  tff(c_16693, plain, (![A_323, C_324, A_325, B_326]: (r1_tarski(A_323, k2_zfmisc_1(C_324, k2_xboole_0(A_325, B_326))) | ~r1_tarski(A_323, k2_zfmisc_1(C_324, B_326)))), inference(superposition, [status(thm), theory('equality')], [c_11774, c_501])).
% 10.08/3.94  tff(c_28, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.08/3.94  tff(c_2013, plain, (![A_95, C_96, B_97]: (k2_xboole_0(k2_zfmisc_1(A_95, C_96), k2_zfmisc_1(B_97, C_96))=k2_zfmisc_1(k2_xboole_0(A_95, B_97), C_96))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.08/3.94  tff(c_9102, plain, (![A_203, A_204, B_205, C_206]: (r1_tarski(A_203, k2_zfmisc_1(k2_xboole_0(A_204, B_205), C_206)) | ~r1_tarski(A_203, k2_zfmisc_1(A_204, C_206)))), inference(superposition, [status(thm), theory('equality')], [c_2013, c_501])).
% 10.08/3.94  tff(c_1741, plain, (![C_84, A_85, B_86]: (k2_xboole_0(k2_zfmisc_1(C_84, A_85), k2_zfmisc_1(C_84, B_86))=k2_zfmisc_1(C_84, k2_xboole_0(A_85, B_86)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 10.08/3.94  tff(c_7281, plain, (![A_177, C_178, A_179, B_180]: (r1_tarski(A_177, k2_zfmisc_1(C_178, k2_xboole_0(A_179, B_180))) | ~r1_tarski(A_177, k2_zfmisc_1(C_178, A_179)))), inference(superposition, [status(thm), theory('equality')], [c_1741, c_501])).
% 10.08/3.94  tff(c_697, plain, (![A_65, C_66, B_67]: (r1_tarski(k2_xboole_0(A_65, C_66), B_67) | ~r1_tarski(C_66, B_67) | ~r1_tarski(A_65, B_67))), inference(cnfTransformation, [status(thm)], [f_45])).
% 10.08/3.94  tff(c_24, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_64])).
% 10.08/3.94  tff(c_734, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_697, c_24])).
% 10.08/3.94  tff(c_855, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitLeft, [status(thm)], [c_734])).
% 10.08/3.94  tff(c_7421, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_7281, c_855])).
% 10.08/3.94  tff(c_9114, plain, (~r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_9102, c_7421])).
% 10.08/3.94  tff(c_9257, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_28, c_9114])).
% 10.08/3.94  tff(c_9258, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_734])).
% 10.08/3.94  tff(c_16839, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_6'))), inference(resolution, [status(thm)], [c_16693, c_9258])).
% 10.08/3.94  tff(c_17160, plain, (~r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(resolution, [status(thm)], [c_17154, c_16839])).
% 10.08/3.94  tff(c_17304, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_26, c_17160])).
% 10.08/3.94  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 10.08/3.94  
% 10.08/3.94  Inference rules
% 10.08/3.94  ----------------------
% 10.08/3.94  #Ref     : 0
% 10.08/3.94  #Sup     : 4726
% 10.08/3.94  #Fact    : 0
% 10.08/3.94  #Define  : 0
% 10.08/3.94  #Split   : 9
% 10.08/3.94  #Chain   : 0
% 10.08/3.94  #Close   : 0
% 10.08/3.94  
% 10.08/3.94  Ordering : KBO
% 10.08/3.94  
% 10.08/3.94  Simplification rules
% 10.08/3.94  ----------------------
% 10.08/3.94  #Subsume      : 851
% 10.08/3.94  #Demod        : 3137
% 10.08/3.94  #Tautology    : 1908
% 10.08/3.94  #SimpNegUnit  : 0
% 10.08/3.94  #BackRed      : 0
% 10.08/3.94  
% 10.08/3.94  #Partial instantiations: 0
% 10.08/3.94  #Strategies tried      : 1
% 10.08/3.94  
% 10.08/3.94  Timing (in seconds)
% 10.08/3.94  ----------------------
% 10.08/3.94  Preprocessing        : 0.46
% 10.08/3.94  Parsing              : 0.26
% 10.08/3.94  CNF conversion       : 0.03
% 10.08/3.94  Main loop            : 2.63
% 10.08/3.94  Inferencing          : 0.56
% 10.08/3.95  Reduction            : 1.37
% 10.08/3.95  Demodulation         : 1.20
% 10.08/3.95  BG Simplification    : 0.08
% 10.08/3.95  Subsumption          : 0.49
% 10.08/3.95  Abstraction          : 0.11
% 10.08/3.95  MUC search           : 0.00
% 10.08/3.95  Cooper               : 0.00
% 10.08/3.95  Total                : 3.13
% 10.08/3.95  Index Insertion      : 0.00
% 10.08/3.95  Index Deletion       : 0.00
% 10.08/3.95  Index Matching       : 0.00
% 10.08/3.95  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:40 EST 2020

% Result     : Theorem 7.48s
% Output     : CNFRefutation 7.77s
% Verified   : 
% Statistics : Number of formulae       :   66 ( 115 expanded)
%              Number of leaves         :   30 (  53 expanded)
%              Depth                    :    7
%              Number of atoms          :   81 ( 164 expanded)
%              Number of equality atoms :   15 (  36 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_45,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_59,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_65,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => ( r1_tarski(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
        & r1_tarski(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t118_zfmisc_1)).

tff(f_35,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_31,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k2_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t8_xboole_1)).

tff(c_12,plain,(
    ! [B_14,A_13] : k2_tarski(B_14,A_13) = k2_tarski(A_13,B_14) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_134,plain,(
    ! [A_57,B_58] : k3_tarski(k2_tarski(A_57,B_58)) = k2_xboole_0(A_57,B_58) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_158,plain,(
    ! [B_61,A_62] : k3_tarski(k2_tarski(B_61,A_62)) = k2_xboole_0(A_62,B_61) ),
    inference(superposition,[status(thm),theory(equality)],[c_12,c_134])).

tff(c_26,plain,(
    ! [A_42,B_43] : k3_tarski(k2_tarski(A_42,B_43)) = k2_xboole_0(A_42,B_43) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_181,plain,(
    ! [B_63,A_64] : k2_xboole_0(B_63,A_64) = k2_xboole_0(A_64,B_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_158,c_26])).

tff(c_8,plain,(
    ! [A_8,B_9] : r1_tarski(A_8,k2_xboole_0(A_8,B_9)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_202,plain,(
    ! [A_64,B_63] : r1_tarski(A_64,k2_xboole_0(B_63,A_64)) ),
    inference(superposition,[status(thm),theory(equality)],[c_181,c_8])).

tff(c_34,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_317,plain,(
    ! [C_78,A_79,B_80] :
      ( r1_tarski(k2_zfmisc_1(C_78,A_79),k2_zfmisc_1(C_78,B_80))
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6,plain,(
    ! [A_6,B_7] :
      ( k3_xboole_0(A_6,B_7) = A_6
      | ~ r1_tarski(A_6,B_7) ) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_6410,plain,(
    ! [C_415,A_416,B_417] :
      ( k3_xboole_0(k2_zfmisc_1(C_415,A_416),k2_zfmisc_1(C_415,B_417)) = k2_zfmisc_1(C_415,A_416)
      | ~ r1_tarski(A_416,B_417) ) ),
    inference(resolution,[status(thm)],[c_317,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_239,plain,(
    ! [A_67,B_68,C_69] :
      ( r1_tarski(A_67,B_68)
      | ~ r1_tarski(A_67,k3_xboole_0(B_68,C_69)) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_254,plain,(
    ! [A_67,B_2,A_1] :
      ( r1_tarski(A_67,B_2)
      | ~ r1_tarski(A_67,k3_xboole_0(A_1,B_2)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_239])).

tff(c_9138,plain,(
    ! [A_512,C_513,B_514,A_515] :
      ( r1_tarski(A_512,k2_zfmisc_1(C_513,B_514))
      | ~ r1_tarski(A_512,k2_zfmisc_1(C_513,A_515))
      | ~ r1_tarski(A_515,B_514) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6410,c_254])).

tff(c_9162,plain,(
    ! [B_514] :
      ( r1_tarski('#skF_2',k2_zfmisc_1('#skF_5',B_514))
      | ~ r1_tarski('#skF_6',B_514) ) ),
    inference(resolution,[status(thm)],[c_34,c_9138])).

tff(c_481,plain,(
    ! [A_94,C_95,B_96] :
      ( r1_tarski(k2_zfmisc_1(A_94,C_95),k2_zfmisc_1(B_96,C_95))
      | ~ r1_tarski(A_94,B_96) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_6092,plain,(
    ! [A_396,C_397,B_398] :
      ( k3_xboole_0(k2_zfmisc_1(A_396,C_397),k2_zfmisc_1(B_398,C_397)) = k2_zfmisc_1(A_396,C_397)
      | ~ r1_tarski(A_396,B_398) ) ),
    inference(resolution,[status(thm)],[c_481,c_6])).

tff(c_9275,plain,(
    ! [A_520,B_521,C_522,A_523] :
      ( r1_tarski(A_520,k2_zfmisc_1(B_521,C_522))
      | ~ r1_tarski(A_520,k2_zfmisc_1(A_523,C_522))
      | ~ r1_tarski(A_523,B_521) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_6092,c_254])).

tff(c_10423,plain,(
    ! [B_552,B_553] :
      ( r1_tarski('#skF_2',k2_zfmisc_1(B_552,B_553))
      | ~ r1_tarski('#skF_5',B_552)
      | ~ r1_tarski('#skF_6',B_553) ) ),
    inference(resolution,[status(thm)],[c_9162,c_9275])).

tff(c_36,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_1396,plain,(
    ! [A_167,C_168,B_169] :
      ( k3_xboole_0(k2_zfmisc_1(A_167,C_168),k2_zfmisc_1(B_169,C_168)) = k2_zfmisc_1(A_167,C_168)
      | ~ r1_tarski(A_167,B_169) ) ),
    inference(resolution,[status(thm)],[c_481,c_6])).

tff(c_2592,plain,(
    ! [A_242,B_243,C_244,A_245] :
      ( r1_tarski(A_242,k2_zfmisc_1(B_243,C_244))
      | ~ r1_tarski(A_242,k2_zfmisc_1(A_245,C_244))
      | ~ r1_tarski(A_245,B_243) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1396,c_254])).

tff(c_2614,plain,(
    ! [B_243] :
      ( r1_tarski('#skF_1',k2_zfmisc_1(B_243,'#skF_4'))
      | ~ r1_tarski('#skF_3',B_243) ) ),
    inference(resolution,[status(thm)],[c_36,c_2592])).

tff(c_1555,plain,(
    ! [C_178,A_179,B_180] :
      ( k3_xboole_0(k2_zfmisc_1(C_178,A_179),k2_zfmisc_1(C_178,B_180)) = k2_zfmisc_1(C_178,A_179)
      | ~ r1_tarski(A_179,B_180) ) ),
    inference(resolution,[status(thm)],[c_317,c_6])).

tff(c_4979,plain,(
    ! [A_313,C_314,B_315,A_316] :
      ( r1_tarski(A_313,k2_zfmisc_1(C_314,B_315))
      | ~ r1_tarski(A_313,k2_zfmisc_1(C_314,A_316))
      | ~ r1_tarski(A_316,B_315) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1555,c_254])).

tff(c_5405,plain,(
    ! [B_325,B_326] :
      ( r1_tarski('#skF_1',k2_zfmisc_1(B_325,B_326))
      | ~ r1_tarski('#skF_4',B_326)
      | ~ r1_tarski('#skF_3',B_325) ) ),
    inference(resolution,[status(thm)],[c_2614,c_4979])).

tff(c_788,plain,(
    ! [A_105,C_106,B_107] :
      ( r1_tarski(k2_xboole_0(A_105,C_106),B_107)
      | ~ r1_tarski(C_106,B_107)
      | ~ r1_tarski(A_105,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_32,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_811,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6')))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(resolution,[status(thm)],[c_788,c_32])).

tff(c_813,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitLeft,[status(thm)],[c_811])).

tff(c_5422,plain,
    ( ~ r1_tarski('#skF_4',k2_xboole_0('#skF_4','#skF_6'))
    | ~ r1_tarski('#skF_3',k2_xboole_0('#skF_3','#skF_5')) ),
    inference(resolution,[status(thm)],[c_5405,c_813])).

tff(c_5437,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_8,c_5422])).

tff(c_5438,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(splitRight,[status(thm)],[c_811])).

tff(c_10440,plain,
    ( ~ r1_tarski('#skF_5',k2_xboole_0('#skF_3','#skF_5'))
    | ~ r1_tarski('#skF_6',k2_xboole_0('#skF_4','#skF_6')) ),
    inference(resolution,[status(thm)],[c_10423,c_5438])).

tff(c_10455,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_202,c_202,c_10440])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n011.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:46:42 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.48/2.65  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.48/2.65  
% 7.48/2.65  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.48/2.66  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.48/2.66  
% 7.48/2.66  %Foreground sorts:
% 7.48/2.66  
% 7.48/2.66  
% 7.48/2.66  %Background operators:
% 7.48/2.66  
% 7.48/2.66  
% 7.48/2.66  %Foreground operators:
% 7.48/2.66  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.48/2.66  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.48/2.66  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.48/2.66  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.48/2.66  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.48/2.66  tff('#skF_5', type, '#skF_5': $i).
% 7.48/2.66  tff('#skF_6', type, '#skF_6': $i).
% 7.48/2.66  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.48/2.66  tff('#skF_2', type, '#skF_2': $i).
% 7.48/2.66  tff('#skF_3', type, '#skF_3': $i).
% 7.48/2.66  tff('#skF_1', type, '#skF_1': $i).
% 7.48/2.66  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.48/2.66  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.48/2.66  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.48/2.66  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.48/2.66  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.48/2.66  tff('#skF_4', type, '#skF_4': $i).
% 7.48/2.66  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.48/2.66  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.48/2.66  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.48/2.66  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.48/2.66  
% 7.77/2.67  tff(f_45, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.77/2.67  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.77/2.67  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.77/2.67  tff(f_72, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 7.77/2.67  tff(f_65, axiom, (![A, B, C]: (r1_tarski(A, B) => (r1_tarski(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C)) & r1_tarski(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t118_zfmisc_1)).
% 7.77/2.67  tff(f_35, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.77/2.67  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.77/2.67  tff(f_31, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 7.77/2.67  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k2_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t8_xboole_1)).
% 7.77/2.67  tff(c_12, plain, (![B_14, A_13]: (k2_tarski(B_14, A_13)=k2_tarski(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.77/2.67  tff(c_134, plain, (![A_57, B_58]: (k3_tarski(k2_tarski(A_57, B_58))=k2_xboole_0(A_57, B_58))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.77/2.67  tff(c_158, plain, (![B_61, A_62]: (k3_tarski(k2_tarski(B_61, A_62))=k2_xboole_0(A_62, B_61))), inference(superposition, [status(thm), theory('equality')], [c_12, c_134])).
% 7.77/2.67  tff(c_26, plain, (![A_42, B_43]: (k3_tarski(k2_tarski(A_42, B_43))=k2_xboole_0(A_42, B_43))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.77/2.67  tff(c_181, plain, (![B_63, A_64]: (k2_xboole_0(B_63, A_64)=k2_xboole_0(A_64, B_63))), inference(superposition, [status(thm), theory('equality')], [c_158, c_26])).
% 7.77/2.67  tff(c_8, plain, (![A_8, B_9]: (r1_tarski(A_8, k2_xboole_0(A_8, B_9)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.77/2.67  tff(c_202, plain, (![A_64, B_63]: (r1_tarski(A_64, k2_xboole_0(B_63, A_64)))), inference(superposition, [status(thm), theory('equality')], [c_181, c_8])).
% 7.77/2.67  tff(c_34, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.77/2.67  tff(c_317, plain, (![C_78, A_79, B_80]: (r1_tarski(k2_zfmisc_1(C_78, A_79), k2_zfmisc_1(C_78, B_80)) | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.77/2.67  tff(c_6, plain, (![A_6, B_7]: (k3_xboole_0(A_6, B_7)=A_6 | ~r1_tarski(A_6, B_7))), inference(cnfTransformation, [status(thm)], [f_35])).
% 7.77/2.67  tff(c_6410, plain, (![C_415, A_416, B_417]: (k3_xboole_0(k2_zfmisc_1(C_415, A_416), k2_zfmisc_1(C_415, B_417))=k2_zfmisc_1(C_415, A_416) | ~r1_tarski(A_416, B_417))), inference(resolution, [status(thm)], [c_317, c_6])).
% 7.77/2.67  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.77/2.67  tff(c_239, plain, (![A_67, B_68, C_69]: (r1_tarski(A_67, B_68) | ~r1_tarski(A_67, k3_xboole_0(B_68, C_69)))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.77/2.67  tff(c_254, plain, (![A_67, B_2, A_1]: (r1_tarski(A_67, B_2) | ~r1_tarski(A_67, k3_xboole_0(A_1, B_2)))), inference(superposition, [status(thm), theory('equality')], [c_2, c_239])).
% 7.77/2.67  tff(c_9138, plain, (![A_512, C_513, B_514, A_515]: (r1_tarski(A_512, k2_zfmisc_1(C_513, B_514)) | ~r1_tarski(A_512, k2_zfmisc_1(C_513, A_515)) | ~r1_tarski(A_515, B_514))), inference(superposition, [status(thm), theory('equality')], [c_6410, c_254])).
% 7.77/2.67  tff(c_9162, plain, (![B_514]: (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', B_514)) | ~r1_tarski('#skF_6', B_514))), inference(resolution, [status(thm)], [c_34, c_9138])).
% 7.77/2.67  tff(c_481, plain, (![A_94, C_95, B_96]: (r1_tarski(k2_zfmisc_1(A_94, C_95), k2_zfmisc_1(B_96, C_95)) | ~r1_tarski(A_94, B_96))), inference(cnfTransformation, [status(thm)], [f_65])).
% 7.77/2.67  tff(c_6092, plain, (![A_396, C_397, B_398]: (k3_xboole_0(k2_zfmisc_1(A_396, C_397), k2_zfmisc_1(B_398, C_397))=k2_zfmisc_1(A_396, C_397) | ~r1_tarski(A_396, B_398))), inference(resolution, [status(thm)], [c_481, c_6])).
% 7.77/2.67  tff(c_9275, plain, (![A_520, B_521, C_522, A_523]: (r1_tarski(A_520, k2_zfmisc_1(B_521, C_522)) | ~r1_tarski(A_520, k2_zfmisc_1(A_523, C_522)) | ~r1_tarski(A_523, B_521))), inference(superposition, [status(thm), theory('equality')], [c_6092, c_254])).
% 7.77/2.67  tff(c_10423, plain, (![B_552, B_553]: (r1_tarski('#skF_2', k2_zfmisc_1(B_552, B_553)) | ~r1_tarski('#skF_5', B_552) | ~r1_tarski('#skF_6', B_553))), inference(resolution, [status(thm)], [c_9162, c_9275])).
% 7.77/2.67  tff(c_36, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.77/2.67  tff(c_1396, plain, (![A_167, C_168, B_169]: (k3_xboole_0(k2_zfmisc_1(A_167, C_168), k2_zfmisc_1(B_169, C_168))=k2_zfmisc_1(A_167, C_168) | ~r1_tarski(A_167, B_169))), inference(resolution, [status(thm)], [c_481, c_6])).
% 7.77/2.67  tff(c_2592, plain, (![A_242, B_243, C_244, A_245]: (r1_tarski(A_242, k2_zfmisc_1(B_243, C_244)) | ~r1_tarski(A_242, k2_zfmisc_1(A_245, C_244)) | ~r1_tarski(A_245, B_243))), inference(superposition, [status(thm), theory('equality')], [c_1396, c_254])).
% 7.77/2.67  tff(c_2614, plain, (![B_243]: (r1_tarski('#skF_1', k2_zfmisc_1(B_243, '#skF_4')) | ~r1_tarski('#skF_3', B_243))), inference(resolution, [status(thm)], [c_36, c_2592])).
% 7.77/2.67  tff(c_1555, plain, (![C_178, A_179, B_180]: (k3_xboole_0(k2_zfmisc_1(C_178, A_179), k2_zfmisc_1(C_178, B_180))=k2_zfmisc_1(C_178, A_179) | ~r1_tarski(A_179, B_180))), inference(resolution, [status(thm)], [c_317, c_6])).
% 7.77/2.67  tff(c_4979, plain, (![A_313, C_314, B_315, A_316]: (r1_tarski(A_313, k2_zfmisc_1(C_314, B_315)) | ~r1_tarski(A_313, k2_zfmisc_1(C_314, A_316)) | ~r1_tarski(A_316, B_315))), inference(superposition, [status(thm), theory('equality')], [c_1555, c_254])).
% 7.77/2.67  tff(c_5405, plain, (![B_325, B_326]: (r1_tarski('#skF_1', k2_zfmisc_1(B_325, B_326)) | ~r1_tarski('#skF_4', B_326) | ~r1_tarski('#skF_3', B_325))), inference(resolution, [status(thm)], [c_2614, c_4979])).
% 7.77/2.67  tff(c_788, plain, (![A_105, C_106, B_107]: (r1_tarski(k2_xboole_0(A_105, C_106), B_107) | ~r1_tarski(C_106, B_107) | ~r1_tarski(A_105, B_107))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.77/2.67  tff(c_32, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.77/2.67  tff(c_811, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6'))) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(resolution, [status(thm)], [c_788, c_32])).
% 7.77/2.67  tff(c_813, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitLeft, [status(thm)], [c_811])).
% 7.77/2.67  tff(c_5422, plain, (~r1_tarski('#skF_4', k2_xboole_0('#skF_4', '#skF_6')) | ~r1_tarski('#skF_3', k2_xboole_0('#skF_3', '#skF_5'))), inference(resolution, [status(thm)], [c_5405, c_813])).
% 7.77/2.67  tff(c_5437, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8, c_8, c_5422])).
% 7.77/2.67  tff(c_5438, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(splitRight, [status(thm)], [c_811])).
% 7.77/2.67  tff(c_10440, plain, (~r1_tarski('#skF_5', k2_xboole_0('#skF_3', '#skF_5')) | ~r1_tarski('#skF_6', k2_xboole_0('#skF_4', '#skF_6'))), inference(resolution, [status(thm)], [c_10423, c_5438])).
% 7.77/2.67  tff(c_10455, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_202, c_202, c_10440])).
% 7.77/2.67  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.77/2.67  
% 7.77/2.67  Inference rules
% 7.77/2.67  ----------------------
% 7.77/2.67  #Ref     : 0
% 7.77/2.67  #Sup     : 2602
% 7.77/2.67  #Fact    : 0
% 7.77/2.67  #Define  : 0
% 7.77/2.67  #Split   : 17
% 7.77/2.67  #Chain   : 0
% 7.77/2.67  #Close   : 0
% 7.77/2.67  
% 7.77/2.67  Ordering : KBO
% 7.77/2.67  
% 7.77/2.67  Simplification rules
% 7.77/2.67  ----------------------
% 7.77/2.67  #Subsume      : 237
% 7.77/2.67  #Demod        : 384
% 7.77/2.67  #Tautology    : 1257
% 7.77/2.67  #SimpNegUnit  : 0
% 7.77/2.67  #BackRed      : 0
% 7.77/2.67  
% 7.77/2.67  #Partial instantiations: 0
% 7.77/2.67  #Strategies tried      : 1
% 7.77/2.67  
% 7.77/2.67  Timing (in seconds)
% 7.77/2.67  ----------------------
% 7.77/2.67  Preprocessing        : 0.30
% 7.77/2.67  Parsing              : 0.16
% 7.77/2.67  CNF conversion       : 0.02
% 7.77/2.67  Main loop            : 1.56
% 7.77/2.67  Inferencing          : 0.46
% 7.77/2.67  Reduction            : 0.63
% 7.77/2.67  Demodulation         : 0.50
% 7.77/2.67  BG Simplification    : 0.05
% 7.77/2.67  Subsumption          : 0.32
% 7.77/2.67  Abstraction          : 0.06
% 7.77/2.67  MUC search           : 0.00
% 7.77/2.67  Cooper               : 0.00
% 7.77/2.67  Total                : 1.89
% 7.77/2.67  Index Insertion      : 0.00
% 7.77/2.67  Index Deletion       : 0.00
% 7.77/2.67  Index Matching       : 0.00
% 7.77/2.67  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 09:53:28 EST 2020

% Result     : Theorem 39.09s
% Output     : CNFRefutation 39.09s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 103 expanded)
%              Number of leaves         :   31 (  49 expanded)
%              Depth                    :    7
%              Number of atoms          :   58 ( 100 expanded)
%              Number of equality atoms :   23 (  61 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

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

tff('#skF_1',type,(
    '#skF_1': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k1_zfmisc_1,type,(
    k1_zfmisc_1: $i > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

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

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k1_zfmisc_1(k3_xboole_0(A,B)) = k3_xboole_0(k1_zfmisc_1(A),k1_zfmisc_1(B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t86_zfmisc_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_157,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_169,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_157])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_787,plain,(
    ! [A_112,B_113,C_114] : k5_xboole_0(k3_xboole_0(A_112,B_113),k3_xboole_0(C_114,B_113)) = k3_xboole_0(k5_xboole_0(A_112,C_114),B_113) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_857,plain,(
    ! [A_5,C_114] : k5_xboole_0(A_5,k3_xboole_0(C_114,A_5)) = k3_xboole_0(k5_xboole_0(A_5,C_114),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_787])).

tff(c_869,plain,(
    ! [A_115,C_116] : k3_xboole_0(A_115,k5_xboole_0(A_115,C_116)) = k4_xboole_0(A_115,C_116) ),
    inference(demodulation,[status(thm),theory(equality)],[c_169,c_2,c_857])).

tff(c_226,plain,(
    ! [A_78,B_79] : k3_xboole_0(k1_zfmisc_1(A_78),k1_zfmisc_1(B_79)) = k1_zfmisc_1(k3_xboole_0(A_78,B_79)) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_86,plain,(
    ! [B_62,A_63] : k3_xboole_0(B_62,A_63) = k3_xboole_0(A_63,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_18,B_19] : r1_tarski(k3_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_101,plain,(
    ! [B_62,A_63] : r1_tarski(k3_xboole_0(B_62,A_63),A_63) ),
    inference(superposition,[status(thm),theory(equality)],[c_86,c_16])).

tff(c_241,plain,(
    ! [A_78,B_79] : r1_tarski(k1_zfmisc_1(k3_xboole_0(A_78,B_79)),k1_zfmisc_1(B_79)) ),
    inference(superposition,[status(thm),theory(equality)],[c_226,c_101])).

tff(c_893,plain,(
    ! [A_115,C_116] : r1_tarski(k1_zfmisc_1(k4_xboole_0(A_115,C_116)),k1_zfmisc_1(k5_xboole_0(A_115,C_116))) ),
    inference(superposition,[status(thm),theory(equality)],[c_869,c_241])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1089,plain,(
    ! [B_140,A_141] : k3_xboole_0(B_140,k5_xboole_0(A_141,B_140)) = k4_xboole_0(B_140,A_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_869])).

tff(c_1117,plain,(
    ! [B_140,A_141] : r1_tarski(k1_zfmisc_1(k4_xboole_0(B_140,A_141)),k1_zfmisc_1(k5_xboole_0(A_141,B_140))) ),
    inference(superposition,[status(thm),theory(equality)],[c_1089,c_241])).

tff(c_10,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(k3_xboole_0(A_9,C_11),B_10)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_902,plain,(
    ! [A_115,C_116,B_10] :
      ( r1_tarski(k4_xboole_0(A_115,C_116),B_10)
      | ~ r1_tarski(A_115,B_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_869,c_10])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_582,plain,(
    ! [A_97,B_98] : k5_xboole_0(k5_xboole_0(A_97,B_98),k3_xboole_0(A_97,B_98)) = k2_xboole_0(A_97,B_98) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_646,plain,(
    ! [A_97,B_98] : k5_xboole_0(k3_xboole_0(A_97,B_98),k5_xboole_0(A_97,B_98)) = k2_xboole_0(A_97,B_98) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_582])).

tff(c_18,plain,(
    ! [A_20,B_21,C_22] : k5_xboole_0(k5_xboole_0(A_20,B_21),C_22) = k5_xboole_0(A_20,k5_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_757,plain,(
    ! [A_109,C_110,B_111] :
      ( r1_tarski(k5_xboole_0(A_109,C_110),B_111)
      | ~ r1_tarski(C_110,B_111)
      | ~ r1_tarski(A_109,B_111) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_17852,plain,(
    ! [A_348,B_349,C_350,B_351] :
      ( r1_tarski(k5_xboole_0(A_348,k5_xboole_0(B_349,C_350)),B_351)
      | ~ r1_tarski(C_350,B_351)
      | ~ r1_tarski(k5_xboole_0(A_348,B_349),B_351) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_757])).

tff(c_18055,plain,(
    ! [A_97,B_98,B_351] :
      ( r1_tarski(k2_xboole_0(A_97,B_98),B_351)
      | ~ r1_tarski(B_98,B_351)
      | ~ r1_tarski(k5_xboole_0(k3_xboole_0(A_97,B_98),A_97),B_351) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_646,c_17852])).

tff(c_95485,plain,(
    ! [A_771,B_772,B_773] :
      ( r1_tarski(k2_xboole_0(A_771,B_772),B_773)
      | ~ r1_tarski(B_772,B_773)
      | ~ r1_tarski(k4_xboole_0(A_771,B_772),B_773) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4,c_18055])).

tff(c_96216,plain,(
    ! [A_785,C_786,B_787] :
      ( r1_tarski(k2_xboole_0(A_785,C_786),B_787)
      | ~ r1_tarski(C_786,B_787)
      | ~ r1_tarski(A_785,B_787) ) ),
    inference(resolution,[status(thm)],[c_902,c_95485])).

tff(c_38,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1'))),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_96221,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_96216,c_38])).

tff(c_96262,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_893,c_1117,c_96221])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n025.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 11:21:20 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 39.09/28.35  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.09/28.36  
% 39.09/28.36  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.09/28.36  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 39.09/28.36  
% 39.09/28.36  %Foreground sorts:
% 39.09/28.36  
% 39.09/28.36  
% 39.09/28.36  %Background operators:
% 39.09/28.36  
% 39.09/28.36  
% 39.09/28.36  %Foreground operators:
% 39.09/28.36  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 39.09/28.36  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 39.09/28.36  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 39.09/28.36  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 39.09/28.36  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 39.09/28.36  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 39.09/28.36  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 39.09/28.36  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 39.09/28.36  tff('#skF_2', type, '#skF_2': $i).
% 39.09/28.36  tff('#skF_1', type, '#skF_1': $i).
% 39.09/28.36  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 39.09/28.36  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 39.09/28.36  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 39.09/28.36  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 39.09/28.36  tff(k3_tarski, type, k3_tarski: $i > $i).
% 39.09/28.36  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 39.09/28.36  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 39.09/28.36  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 39.09/28.36  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 39.09/28.36  
% 39.09/28.37  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 39.09/28.37  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 39.09/28.37  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 39.09/28.37  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t112_xboole_1)).
% 39.09/28.37  tff(f_67, axiom, (![A, B]: (k1_zfmisc_1(k3_xboole_0(A, B)) = k3_xboole_0(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_zfmisc_1)).
% 39.09/28.37  tff(f_47, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 39.09/28.37  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 39.09/28.37  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t108_xboole_1)).
% 39.09/28.37  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 39.09/28.37  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 39.09/28.37  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t110_xboole_1)).
% 39.09/28.37  tff(f_70, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A, B)), k1_zfmisc_1(k4_xboole_0(B, A))), k1_zfmisc_1(k5_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 39.09/28.37  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 39.09/28.37  tff(c_157, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_33])).
% 39.09/28.37  tff(c_169, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_157])).
% 39.09/28.37  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 39.09/28.37  tff(c_787, plain, (![A_112, B_113, C_114]: (k5_xboole_0(k3_xboole_0(A_112, B_113), k3_xboole_0(C_114, B_113))=k3_xboole_0(k5_xboole_0(A_112, C_114), B_113))), inference(cnfTransformation, [status(thm)], [f_45])).
% 39.09/28.37  tff(c_857, plain, (![A_5, C_114]: (k5_xboole_0(A_5, k3_xboole_0(C_114, A_5))=k3_xboole_0(k5_xboole_0(A_5, C_114), A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_787])).
% 39.09/28.37  tff(c_869, plain, (![A_115, C_116]: (k3_xboole_0(A_115, k5_xboole_0(A_115, C_116))=k4_xboole_0(A_115, C_116))), inference(demodulation, [status(thm), theory('equality')], [c_169, c_2, c_857])).
% 39.09/28.37  tff(c_226, plain, (![A_78, B_79]: (k3_xboole_0(k1_zfmisc_1(A_78), k1_zfmisc_1(B_79))=k1_zfmisc_1(k3_xboole_0(A_78, B_79)))), inference(cnfTransformation, [status(thm)], [f_67])).
% 39.09/28.37  tff(c_86, plain, (![B_62, A_63]: (k3_xboole_0(B_62, A_63)=k3_xboole_0(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_27])).
% 39.09/28.37  tff(c_16, plain, (![A_18, B_19]: (r1_tarski(k3_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 39.09/28.37  tff(c_101, plain, (![B_62, A_63]: (r1_tarski(k3_xboole_0(B_62, A_63), A_63))), inference(superposition, [status(thm), theory('equality')], [c_86, c_16])).
% 39.09/28.37  tff(c_241, plain, (![A_78, B_79]: (r1_tarski(k1_zfmisc_1(k3_xboole_0(A_78, B_79)), k1_zfmisc_1(B_79)))), inference(superposition, [status(thm), theory('equality')], [c_226, c_101])).
% 39.09/28.37  tff(c_893, plain, (![A_115, C_116]: (r1_tarski(k1_zfmisc_1(k4_xboole_0(A_115, C_116)), k1_zfmisc_1(k5_xboole_0(A_115, C_116))))), inference(superposition, [status(thm), theory('equality')], [c_869, c_241])).
% 39.09/28.37  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 39.09/28.37  tff(c_1089, plain, (![B_140, A_141]: (k3_xboole_0(B_140, k5_xboole_0(A_141, B_140))=k4_xboole_0(B_140, A_141))), inference(superposition, [status(thm), theory('equality')], [c_4, c_869])).
% 39.09/28.37  tff(c_1117, plain, (![B_140, A_141]: (r1_tarski(k1_zfmisc_1(k4_xboole_0(B_140, A_141)), k1_zfmisc_1(k5_xboole_0(A_141, B_140))))), inference(superposition, [status(thm), theory('equality')], [c_1089, c_241])).
% 39.09/28.37  tff(c_10, plain, (![A_9, C_11, B_10]: (r1_tarski(k3_xboole_0(A_9, C_11), B_10) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 39.09/28.37  tff(c_902, plain, (![A_115, C_116, B_10]: (r1_tarski(k4_xboole_0(A_115, C_116), B_10) | ~r1_tarski(A_115, B_10))), inference(superposition, [status(thm), theory('equality')], [c_869, c_10])).
% 39.09/28.37  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 39.09/28.37  tff(c_582, plain, (![A_97, B_98]: (k5_xboole_0(k5_xboole_0(A_97, B_98), k3_xboole_0(A_97, B_98))=k2_xboole_0(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_51])).
% 39.09/28.37  tff(c_646, plain, (![A_97, B_98]: (k5_xboole_0(k3_xboole_0(A_97, B_98), k5_xboole_0(A_97, B_98))=k2_xboole_0(A_97, B_98))), inference(superposition, [status(thm), theory('equality')], [c_4, c_582])).
% 39.09/28.37  tff(c_18, plain, (![A_20, B_21, C_22]: (k5_xboole_0(k5_xboole_0(A_20, B_21), C_22)=k5_xboole_0(A_20, k5_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 39.09/28.37  tff(c_757, plain, (![A_109, C_110, B_111]: (r1_tarski(k5_xboole_0(A_109, C_110), B_111) | ~r1_tarski(C_110, B_111) | ~r1_tarski(A_109, B_111))), inference(cnfTransformation, [status(thm)], [f_43])).
% 39.09/28.37  tff(c_17852, plain, (![A_348, B_349, C_350, B_351]: (r1_tarski(k5_xboole_0(A_348, k5_xboole_0(B_349, C_350)), B_351) | ~r1_tarski(C_350, B_351) | ~r1_tarski(k5_xboole_0(A_348, B_349), B_351))), inference(superposition, [status(thm), theory('equality')], [c_18, c_757])).
% 39.09/28.37  tff(c_18055, plain, (![A_97, B_98, B_351]: (r1_tarski(k2_xboole_0(A_97, B_98), B_351) | ~r1_tarski(B_98, B_351) | ~r1_tarski(k5_xboole_0(k3_xboole_0(A_97, B_98), A_97), B_351))), inference(superposition, [status(thm), theory('equality')], [c_646, c_17852])).
% 39.09/28.37  tff(c_95485, plain, (![A_771, B_772, B_773]: (r1_tarski(k2_xboole_0(A_771, B_772), B_773) | ~r1_tarski(B_772, B_773) | ~r1_tarski(k4_xboole_0(A_771, B_772), B_773))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_4, c_18055])).
% 39.09/28.37  tff(c_96216, plain, (![A_785, C_786, B_787]: (r1_tarski(k2_xboole_0(A_785, C_786), B_787) | ~r1_tarski(C_786, B_787) | ~r1_tarski(A_785, B_787))), inference(resolution, [status(thm)], [c_902, c_95485])).
% 39.09/28.37  tff(c_38, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1'))), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 39.09/28.37  tff(c_96221, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_96216, c_38])).
% 39.09/28.37  tff(c_96262, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_893, c_1117, c_96221])).
% 39.09/28.37  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 39.09/28.37  
% 39.09/28.37  Inference rules
% 39.09/28.37  ----------------------
% 39.09/28.37  #Ref     : 0
% 39.09/28.37  #Sup     : 26079
% 39.09/28.37  #Fact    : 0
% 39.09/28.37  #Define  : 0
% 39.09/28.37  #Split   : 0
% 39.09/28.37  #Chain   : 0
% 39.09/28.37  #Close   : 0
% 39.09/28.37  
% 39.09/28.37  Ordering : KBO
% 39.09/28.37  
% 39.09/28.37  Simplification rules
% 39.09/28.37  ----------------------
% 39.09/28.37  #Subsume      : 1156
% 39.09/28.37  #Demod        : 26408
% 39.09/28.37  #Tautology    : 5879
% 39.09/28.37  #SimpNegUnit  : 0
% 39.09/28.37  #BackRed      : 15
% 39.09/28.37  
% 39.09/28.37  #Partial instantiations: 0
% 39.09/28.37  #Strategies tried      : 1
% 39.09/28.37  
% 39.09/28.37  Timing (in seconds)
% 39.09/28.37  ----------------------
% 39.09/28.38  Preprocessing        : 0.32
% 39.09/28.38  Parsing              : 0.17
% 39.09/28.38  CNF conversion       : 0.02
% 39.09/28.38  Main loop            : 27.28
% 39.09/28.38  Inferencing          : 2.24
% 39.09/28.38  Reduction            : 19.27
% 39.09/28.38  Demodulation         : 18.37
% 39.09/28.38  BG Simplification    : 0.46
% 39.09/28.38  Subsumption          : 4.24
% 39.09/28.38  Abstraction          : 0.62
% 39.09/28.38  MUC search           : 0.00
% 39.09/28.38  Cooper               : 0.00
% 39.09/28.38  Total                : 27.63
% 39.09/28.38  Index Insertion      : 0.00
% 39.09/28.38  Index Deletion       : 0.00
% 39.09/28.38  Index Matching       : 0.00
% 39.09/28.38  BG Taut test         : 0.00
%------------------------------------------------------------------------------

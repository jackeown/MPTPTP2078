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
% DateTime   : Thu Dec  3 09:53:29 EST 2020

% Result     : Theorem 35.20s
% Output     : CNFRefutation 35.20s
% Verified   : 
% Statistics : Number of formulae       :   61 ( 136 expanded)
%              Number of leaves         :   29 (  58 expanded)
%              Depth                    :    9
%              Number of atoms          :   58 ( 147 expanded)
%              Number of equality atoms :   20 (  80 expanded)
%              Maximal formula depth    :    8 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1

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

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k3_xboole_0(A,B),k3_xboole_0(C,B)) = k3_xboole_0(k5_xboole_0(A,C),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t112_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => r1_tarski(k1_zfmisc_1(A),k1_zfmisc_1(B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(k3_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t108_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,B) )
     => r1_tarski(k5_xboole_0(A,C),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t110_xboole_1)).

tff(f_68,negated_conjecture,(
    ~ ! [A,B] : r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A,B)),k1_zfmisc_1(k4_xboole_0(B,A))),k1_zfmisc_1(k5_xboole_0(A,B))) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t86_zfmisc_1)).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_163,plain,(
    ! [A_60,B_61] : k5_xboole_0(A_60,k3_xboole_0(A_60,B_61)) = k4_xboole_0(A_60,B_61) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_175,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_163])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_1027,plain,(
    ! [A_99,B_100,C_101] : k5_xboole_0(k3_xboole_0(A_99,B_100),k3_xboole_0(C_101,B_100)) = k3_xboole_0(k5_xboole_0(A_99,C_101),B_100) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_1100,plain,(
    ! [A_5,C_101] : k5_xboole_0(A_5,k3_xboole_0(C_101,A_5)) = k3_xboole_0(k5_xboole_0(A_5,C_101),A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_1027])).

tff(c_1112,plain,(
    ! [A_102,C_103] : k3_xboole_0(A_102,k5_xboole_0(A_102,C_103)) = k4_xboole_0(A_102,C_103) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_2,c_1100])).

tff(c_82,plain,(
    ! [B_49,A_50] : k3_xboole_0(B_49,A_50) = k3_xboole_0(A_50,B_49) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_16,plain,(
    ! [A_18,B_19] : r1_tarski(k3_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_97,plain,(
    ! [B_49,A_50] : r1_tarski(k3_xboole_0(B_49,A_50),A_50) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_16])).

tff(c_1148,plain,(
    ! [A_102,C_103] : r1_tarski(k4_xboole_0(A_102,C_103),k5_xboole_0(A_102,C_103)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1112,c_97])).

tff(c_32,plain,(
    ! [A_41,B_42] :
      ( r1_tarski(k1_zfmisc_1(A_41),k1_zfmisc_1(B_42))
      | ~ r1_tarski(A_41,B_42) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1206,plain,(
    ! [A_106,C_107] : r1_tarski(k4_xboole_0(A_106,C_107),k5_xboole_0(A_106,C_107)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1112,c_97])).

tff(c_1245,plain,(
    ! [A_3,B_4] : r1_tarski(k4_xboole_0(A_3,B_4),k5_xboole_0(B_4,A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1206])).

tff(c_10,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(k3_xboole_0(A_9,C_11),B_10)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1145,plain,(
    ! [A_102,C_103,B_10] :
      ( r1_tarski(k4_xboole_0(A_102,C_103),B_10)
      | ~ r1_tarski(A_102,B_10) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1112,c_10])).

tff(c_310,plain,(
    ! [A_76,B_77,C_78] : k5_xboole_0(k5_xboole_0(A_76,B_77),C_78) = k5_xboole_0(A_76,k5_xboole_0(B_77,C_78)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_20,plain,(
    ! [A_23,B_24] : k5_xboole_0(k5_xboole_0(A_23,B_24),k3_xboole_0(A_23,B_24)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_327,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k5_xboole_0(B_77,k3_xboole_0(A_76,B_77))) = k2_xboole_0(A_76,B_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_310,c_20])).

tff(c_402,plain,(
    ! [A_76,B_77] : k5_xboole_0(A_76,k4_xboole_0(B_77,A_76)) = k2_xboole_0(A_76,B_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_175,c_327])).

tff(c_749,plain,(
    ! [A_92,C_93,B_94] :
      ( r1_tarski(k5_xboole_0(A_92,C_93),B_94)
      | ~ r1_tarski(C_93,B_94)
      | ~ r1_tarski(A_92,B_94) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_82008,plain,(
    ! [A_633,B_634,B_635] :
      ( r1_tarski(k2_xboole_0(A_633,B_634),B_635)
      | ~ r1_tarski(k4_xboole_0(B_634,A_633),B_635)
      | ~ r1_tarski(A_633,B_635) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_402,c_749])).

tff(c_82782,plain,(
    ! [C_647,A_648,B_649] :
      ( r1_tarski(k2_xboole_0(C_647,A_648),B_649)
      | ~ r1_tarski(C_647,B_649)
      | ~ r1_tarski(A_648,B_649) ) ),
    inference(resolution,[status(thm)],[c_1145,c_82008])).

tff(c_34,plain,(
    ~ r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1'))),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_82825,plain,
    ( ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2')))
    | ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(resolution,[status(thm)],[c_82782,c_34])).

tff(c_82827,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2','#skF_1')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitLeft,[status(thm)],[c_82825])).

tff(c_82830,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_2','#skF_1'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_82827])).

tff(c_82834,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1245,c_82830])).

tff(c_82835,plain,(
    ~ r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1','#skF_2')),k1_zfmisc_1(k5_xboole_0('#skF_1','#skF_2'))) ),
    inference(splitRight,[status(thm)],[c_82825])).

tff(c_82839,plain,(
    ~ r1_tarski(k4_xboole_0('#skF_1','#skF_2'),k5_xboole_0('#skF_1','#skF_2')) ),
    inference(resolution,[status(thm)],[c_32,c_82835])).

tff(c_82843,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1148,c_82839])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n014.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:51:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 35.20/24.83  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.20/24.83  
% 35.20/24.83  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.20/24.84  %$ r1_tarski > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_zfmisc_1 > #skF_2 > #skF_1
% 35.20/24.84  
% 35.20/24.84  %Foreground sorts:
% 35.20/24.84  
% 35.20/24.84  
% 35.20/24.84  %Background operators:
% 35.20/24.84  
% 35.20/24.84  
% 35.20/24.84  %Foreground operators:
% 35.20/24.84  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 35.20/24.84  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 35.20/24.84  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 35.20/24.84  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 35.20/24.84  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 35.20/24.84  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 35.20/24.84  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 35.20/24.84  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 35.20/24.84  tff('#skF_2', type, '#skF_2': $i).
% 35.20/24.84  tff('#skF_1', type, '#skF_1': $i).
% 35.20/24.84  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 35.20/24.84  tff(k1_zfmisc_1, type, k1_zfmisc_1: $i > $i).
% 35.20/24.84  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 35.20/24.84  tff(k3_tarski, type, k3_tarski: $i > $i).
% 35.20/24.84  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 35.20/24.84  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 35.20/24.84  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 35.20/24.84  
% 35.20/24.85  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 35.20/24.85  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 35.20/24.85  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 35.20/24.85  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k3_xboole_0(A, B), k3_xboole_0(C, B)) = k3_xboole_0(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t112_xboole_1)).
% 35.20/24.85  tff(f_47, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 35.20/24.85  tff(f_65, axiom, (![A, B]: (r1_tarski(A, B) => r1_tarski(k1_zfmisc_1(A), k1_zfmisc_1(B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_zfmisc_1)).
% 35.20/24.85  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 35.20/24.85  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(k3_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t108_xboole_1)).
% 35.20/24.85  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 35.20/24.85  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 35.20/24.85  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(C, B)) => r1_tarski(k5_xboole_0(A, C), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t110_xboole_1)).
% 35.20/24.85  tff(f_68, negated_conjecture, ~(![A, B]: r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0(A, B)), k1_zfmisc_1(k4_xboole_0(B, A))), k1_zfmisc_1(k5_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t86_zfmisc_1)).
% 35.20/24.85  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 35.20/24.85  tff(c_163, plain, (![A_60, B_61]: (k5_xboole_0(A_60, k3_xboole_0(A_60, B_61))=k4_xboole_0(A_60, B_61))), inference(cnfTransformation, [status(thm)], [f_33])).
% 35.20/24.85  tff(c_175, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_163])).
% 35.20/24.85  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 35.20/24.85  tff(c_1027, plain, (![A_99, B_100, C_101]: (k5_xboole_0(k3_xboole_0(A_99, B_100), k3_xboole_0(C_101, B_100))=k3_xboole_0(k5_xboole_0(A_99, C_101), B_100))), inference(cnfTransformation, [status(thm)], [f_45])).
% 35.20/24.85  tff(c_1100, plain, (![A_5, C_101]: (k5_xboole_0(A_5, k3_xboole_0(C_101, A_5))=k3_xboole_0(k5_xboole_0(A_5, C_101), A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_1027])).
% 35.20/24.85  tff(c_1112, plain, (![A_102, C_103]: (k3_xboole_0(A_102, k5_xboole_0(A_102, C_103))=k4_xboole_0(A_102, C_103))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_2, c_1100])).
% 35.20/24.85  tff(c_82, plain, (![B_49, A_50]: (k3_xboole_0(B_49, A_50)=k3_xboole_0(A_50, B_49))), inference(cnfTransformation, [status(thm)], [f_27])).
% 35.20/24.85  tff(c_16, plain, (![A_18, B_19]: (r1_tarski(k3_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 35.20/24.85  tff(c_97, plain, (![B_49, A_50]: (r1_tarski(k3_xboole_0(B_49, A_50), A_50))), inference(superposition, [status(thm), theory('equality')], [c_82, c_16])).
% 35.20/24.85  tff(c_1148, plain, (![A_102, C_103]: (r1_tarski(k4_xboole_0(A_102, C_103), k5_xboole_0(A_102, C_103)))), inference(superposition, [status(thm), theory('equality')], [c_1112, c_97])).
% 35.20/24.85  tff(c_32, plain, (![A_41, B_42]: (r1_tarski(k1_zfmisc_1(A_41), k1_zfmisc_1(B_42)) | ~r1_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_65])).
% 35.20/24.85  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 35.20/24.85  tff(c_1206, plain, (![A_106, C_107]: (r1_tarski(k4_xboole_0(A_106, C_107), k5_xboole_0(A_106, C_107)))), inference(superposition, [status(thm), theory('equality')], [c_1112, c_97])).
% 35.20/24.85  tff(c_1245, plain, (![A_3, B_4]: (r1_tarski(k4_xboole_0(A_3, B_4), k5_xboole_0(B_4, A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1206])).
% 35.20/24.85  tff(c_10, plain, (![A_9, C_11, B_10]: (r1_tarski(k3_xboole_0(A_9, C_11), B_10) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 35.20/24.85  tff(c_1145, plain, (![A_102, C_103, B_10]: (r1_tarski(k4_xboole_0(A_102, C_103), B_10) | ~r1_tarski(A_102, B_10))), inference(superposition, [status(thm), theory('equality')], [c_1112, c_10])).
% 35.20/24.85  tff(c_310, plain, (![A_76, B_77, C_78]: (k5_xboole_0(k5_xboole_0(A_76, B_77), C_78)=k5_xboole_0(A_76, k5_xboole_0(B_77, C_78)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 35.20/24.85  tff(c_20, plain, (![A_23, B_24]: (k5_xboole_0(k5_xboole_0(A_23, B_24), k3_xboole_0(A_23, B_24))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_51])).
% 35.20/24.85  tff(c_327, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k5_xboole_0(B_77, k3_xboole_0(A_76, B_77)))=k2_xboole_0(A_76, B_77))), inference(superposition, [status(thm), theory('equality')], [c_310, c_20])).
% 35.20/24.85  tff(c_402, plain, (![A_76, B_77]: (k5_xboole_0(A_76, k4_xboole_0(B_77, A_76))=k2_xboole_0(A_76, B_77))), inference(demodulation, [status(thm), theory('equality')], [c_175, c_327])).
% 35.20/24.85  tff(c_749, plain, (![A_92, C_93, B_94]: (r1_tarski(k5_xboole_0(A_92, C_93), B_94) | ~r1_tarski(C_93, B_94) | ~r1_tarski(A_92, B_94))), inference(cnfTransformation, [status(thm)], [f_43])).
% 35.20/24.85  tff(c_82008, plain, (![A_633, B_634, B_635]: (r1_tarski(k2_xboole_0(A_633, B_634), B_635) | ~r1_tarski(k4_xboole_0(B_634, A_633), B_635) | ~r1_tarski(A_633, B_635))), inference(superposition, [status(thm), theory('equality')], [c_402, c_749])).
% 35.20/24.85  tff(c_82782, plain, (![C_647, A_648, B_649]: (r1_tarski(k2_xboole_0(C_647, A_648), B_649) | ~r1_tarski(C_647, B_649) | ~r1_tarski(A_648, B_649))), inference(resolution, [status(thm)], [c_1145, c_82008])).
% 35.20/24.85  tff(c_34, plain, (~r1_tarski(k2_xboole_0(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1'))), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(cnfTransformation, [status(thm)], [f_68])).
% 35.20/24.85  tff(c_82825, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2'))) | ~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(resolution, [status(thm)], [c_82782, c_34])).
% 35.20/24.85  tff(c_82827, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_2', '#skF_1')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitLeft, [status(thm)], [c_82825])).
% 35.20/24.85  tff(c_82830, plain, (~r1_tarski(k4_xboole_0('#skF_2', '#skF_1'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_82827])).
% 35.20/24.85  tff(c_82834, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1245, c_82830])).
% 35.20/24.85  tff(c_82835, plain, (~r1_tarski(k1_zfmisc_1(k4_xboole_0('#skF_1', '#skF_2')), k1_zfmisc_1(k5_xboole_0('#skF_1', '#skF_2')))), inference(splitRight, [status(thm)], [c_82825])).
% 35.20/24.85  tff(c_82839, plain, (~r1_tarski(k4_xboole_0('#skF_1', '#skF_2'), k5_xboole_0('#skF_1', '#skF_2'))), inference(resolution, [status(thm)], [c_32, c_82835])).
% 35.20/24.85  tff(c_82843, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1148, c_82839])).
% 35.20/24.85  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 35.20/24.85  
% 35.20/24.85  Inference rules
% 35.20/24.85  ----------------------
% 35.20/24.85  #Ref     : 0
% 35.20/24.85  #Sup     : 22171
% 35.20/24.85  #Fact    : 0
% 35.20/24.85  #Define  : 0
% 35.20/24.85  #Split   : 1
% 35.20/24.85  #Chain   : 0
% 35.20/24.85  #Close   : 0
% 35.20/24.85  
% 35.20/24.85  Ordering : KBO
% 35.20/24.85  
% 35.20/24.85  Simplification rules
% 35.20/24.85  ----------------------
% 35.20/24.85  #Subsume      : 1103
% 35.20/24.85  #Demod        : 24448
% 35.20/24.85  #Tautology    : 4950
% 35.20/24.85  #SimpNegUnit  : 0
% 35.20/24.85  #BackRed      : 17
% 35.20/24.85  
% 35.20/24.85  #Partial instantiations: 0
% 35.20/24.85  #Strategies tried      : 1
% 35.20/24.85  
% 35.20/24.85  Timing (in seconds)
% 35.20/24.85  ----------------------
% 35.20/24.85  Preprocessing        : 0.32
% 35.20/24.85  Parsing              : 0.18
% 35.20/24.85  CNF conversion       : 0.02
% 35.20/24.85  Main loop            : 23.77
% 35.20/24.85  Inferencing          : 2.01
% 35.20/24.85  Reduction            : 17.12
% 35.20/24.85  Demodulation         : 16.34
% 35.20/24.85  BG Simplification    : 0.42
% 35.20/24.85  Subsumption          : 3.34
% 35.20/24.85  Abstraction          : 0.60
% 35.20/24.85  MUC search           : 0.00
% 35.20/24.85  Cooper               : 0.00
% 35.20/24.85  Total                : 24.12
% 35.20/24.85  Index Insertion      : 0.00
% 35.20/24.85  Index Deletion       : 0.00
% 35.20/24.85  Index Matching       : 0.00
% 35.20/24.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------

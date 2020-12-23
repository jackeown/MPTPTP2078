%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n023.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:50 EST 2020

% Result     : Theorem 12.84s
% Output     : CNFRefutation 12.84s
% Verified   : 
% Statistics : Number of formulae       :   62 ( 140 expanded)
%              Number of leaves         :   28 (  60 expanded)
%              Depth                    :   13
%              Number of atoms          :   50 ( 132 expanded)
%              Number of equality atoms :   39 ( 117 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_72,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( ~ r2_hidden(A,C)
          & ~ r2_hidden(B,C)
          & C != k4_xboole_0(k2_xboole_0(C,k2_tarski(A,B)),k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t145_zfmisc_1)).

tff(f_61,axiom,(
    ! [A,B,C] :
      ~ ( ~ r2_hidden(A,C)
        & ~ r2_hidden(B,C)
        & C != k4_xboole_0(C,k2_tarski(A,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t144_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_31,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(c_34,plain,(
    ~ r2_hidden('#skF_1','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_32,plain,(
    ~ r2_hidden('#skF_2','#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_28,plain,(
    ! [C_43,A_41,B_42] :
      ( k4_xboole_0(C_43,k2_tarski(A_41,B_42)) = C_43
      | r2_hidden(B_42,C_43)
      | r2_hidden(A_41,C_43) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_2,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(A_1,B_2)) = k4_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_211,plain,(
    ! [A_66,B_67,C_68] : k5_xboole_0(k5_xboole_0(A_66,B_67),C_68) = k5_xboole_0(A_66,k5_xboole_0(B_67,C_68)) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(k5_xboole_0(A_10,B_11),k2_xboole_0(A_10,B_11)) = k3_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1567,plain,(
    ! [A_121,B_122] : k5_xboole_0(A_121,k5_xboole_0(B_122,k2_xboole_0(A_121,B_122))) = k3_xboole_0(A_121,B_122) ),
    inference(superposition,[status(thm),theory(equality)],[c_211,c_12])).

tff(c_6,plain,(
    ! [A_5] : k5_xboole_0(A_5,k1_xboole_0) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_485,plain,(
    ! [A_78,C_79] : k5_xboole_0(A_78,k5_xboole_0(A_78,C_79)) = k5_xboole_0(k1_xboole_0,C_79) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_211])).

tff(c_557,plain,(
    ! [A_9] : k5_xboole_0(k1_xboole_0,A_9) = k5_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_485])).

tff(c_574,plain,(
    ! [A_9] : k5_xboole_0(k1_xboole_0,A_9) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_557])).

tff(c_287,plain,(
    ! [A_9,C_68] : k5_xboole_0(A_9,k5_xboole_0(A_9,C_68)) = k5_xboole_0(k1_xboole_0,C_68) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_211])).

tff(c_575,plain,(
    ! [A_9,C_68] : k5_xboole_0(A_9,k5_xboole_0(A_9,C_68)) = C_68 ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_287])).

tff(c_1582,plain,(
    ! [B_122,A_121] : k5_xboole_0(B_122,k2_xboole_0(A_121,B_122)) = k5_xboole_0(A_121,k3_xboole_0(A_121,B_122)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1567,c_575])).

tff(c_2553,plain,(
    ! [B_144,A_145] : k5_xboole_0(B_144,k2_xboole_0(A_145,B_144)) = k4_xboole_0(A_145,B_144) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_1582])).

tff(c_3975,plain,(
    ! [B_169,A_170] : k5_xboole_0(B_169,k4_xboole_0(A_170,B_169)) = k2_xboole_0(A_170,B_169) ),
    inference(superposition,[status(thm),theory(equality)],[c_2553,c_575])).

tff(c_14,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k4_xboole_0(B_13,A_12)) = k2_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_4019,plain,(
    ! [B_169,A_170] : k2_xboole_0(B_169,A_170) = k2_xboole_0(A_170,B_169) ),
    inference(superposition,[status(thm),theory(equality)],[c_3975,c_14])).

tff(c_640,plain,(
    ! [A_81,C_82] : k5_xboole_0(A_81,k5_xboole_0(A_81,C_82)) = C_82 ),
    inference(demodulation,[status(thm),theory(equality)],[c_574,c_287])).

tff(c_692,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k2_xboole_0(A_12,B_13)) = k4_xboole_0(B_13,A_12) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_640])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_88,plain,(
    ! [A_52,B_53] : k5_xboole_0(A_52,k3_xboole_0(A_52,B_53)) = k4_xboole_0(A_52,B_53) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_97,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_88])).

tff(c_101,plain,(
    ! [A_54,B_55] : k4_xboole_0(A_54,k2_xboole_0(A_54,B_55)) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_97])).

tff(c_106,plain,(
    ! [A_54,B_55] : k5_xboole_0(k2_xboole_0(A_54,B_55),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_54,B_55),A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_101,c_14])).

tff(c_110,plain,(
    ! [A_54,B_55] : k2_xboole_0(k2_xboole_0(A_54,B_55),A_54) = k2_xboole_0(A_54,B_55) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_106])).

tff(c_2629,plain,(
    ! [A_54,B_55] : k5_xboole_0(A_54,k2_xboole_0(A_54,B_55)) = k4_xboole_0(k2_xboole_0(A_54,B_55),A_54) ),
    inference(superposition,[status(thm),theory(equality)],[c_110,c_2553])).

tff(c_7880,plain,(
    ! [A_214,B_215] : k4_xboole_0(k2_xboole_0(A_214,B_215),A_214) = k4_xboole_0(B_215,A_214) ),
    inference(demodulation,[status(thm),theory(equality)],[c_692,c_2629])).

tff(c_7960,plain,(
    ! [A_170,B_169] : k4_xboole_0(k2_xboole_0(A_170,B_169),B_169) = k4_xboole_0(A_170,B_169) ),
    inference(superposition,[status(thm),theory(equality)],[c_4019,c_7880])).

tff(c_30,plain,(
    k4_xboole_0(k2_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')),k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_30708,plain,(
    k4_xboole_0('#skF_3',k2_tarski('#skF_1','#skF_2')) != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_7960,c_30])).

tff(c_30934,plain,
    ( r2_hidden('#skF_2','#skF_3')
    | r2_hidden('#skF_1','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_28,c_30708])).

tff(c_30938,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_34,c_32,c_30934])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n023.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 15:16:50 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.22/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 12.84/6.27  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.84/6.27  
% 12.84/6.27  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.84/6.28  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 12.84/6.28  
% 12.84/6.28  %Foreground sorts:
% 12.84/6.28  
% 12.84/6.28  
% 12.84/6.28  %Background operators:
% 12.84/6.28  
% 12.84/6.28  
% 12.84/6.28  %Foreground operators:
% 12.84/6.28  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 12.84/6.28  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 12.84/6.28  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 12.84/6.28  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 12.84/6.28  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 12.84/6.28  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 12.84/6.28  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 12.84/6.28  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 12.84/6.28  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 12.84/6.28  tff('#skF_2', type, '#skF_2': $i).
% 12.84/6.28  tff('#skF_3', type, '#skF_3': $i).
% 12.84/6.28  tff('#skF_1', type, '#skF_1': $i).
% 12.84/6.28  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 12.84/6.28  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 12.84/6.28  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 12.84/6.28  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 12.84/6.28  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 12.84/6.28  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 12.84/6.28  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 12.84/6.28  
% 12.84/6.29  tff(f_72, negated_conjecture, ~(![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(k2_xboole_0(C, k2_tarski(A, B)), k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t145_zfmisc_1)).
% 12.84/6.29  tff(f_61, axiom, (![A, B, C]: ~((~r2_hidden(A, C) & ~r2_hidden(B, C)) & ~(C = k4_xboole_0(C, k2_tarski(A, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t144_zfmisc_1)).
% 12.84/6.29  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 12.84/6.29  tff(f_33, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 12.84/6.29  tff(f_37, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 12.84/6.29  tff(f_31, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 12.84/6.29  tff(f_35, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 12.84/6.29  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 12.84/6.29  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 12.84/6.29  tff(c_34, plain, (~r2_hidden('#skF_1', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.84/6.29  tff(c_32, plain, (~r2_hidden('#skF_2', '#skF_3')), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.84/6.29  tff(c_28, plain, (![C_43, A_41, B_42]: (k4_xboole_0(C_43, k2_tarski(A_41, B_42))=C_43 | r2_hidden(B_42, C_43) | r2_hidden(A_41, C_43))), inference(cnfTransformation, [status(thm)], [f_61])).
% 12.84/6.29  tff(c_2, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(A_1, B_2))=k4_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.84/6.29  tff(c_211, plain, (![A_66, B_67, C_68]: (k5_xboole_0(k5_xboole_0(A_66, B_67), C_68)=k5_xboole_0(A_66, k5_xboole_0(B_67, C_68)))), inference(cnfTransformation, [status(thm)], [f_33])).
% 12.84/6.29  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(k5_xboole_0(A_10, B_11), k2_xboole_0(A_10, B_11))=k3_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_37])).
% 12.84/6.29  tff(c_1567, plain, (![A_121, B_122]: (k5_xboole_0(A_121, k5_xboole_0(B_122, k2_xboole_0(A_121, B_122)))=k3_xboole_0(A_121, B_122))), inference(superposition, [status(thm), theory('equality')], [c_211, c_12])).
% 12.84/6.29  tff(c_6, plain, (![A_5]: (k5_xboole_0(A_5, k1_xboole_0)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 12.84/6.29  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 12.84/6.29  tff(c_485, plain, (![A_78, C_79]: (k5_xboole_0(A_78, k5_xboole_0(A_78, C_79))=k5_xboole_0(k1_xboole_0, C_79))), inference(superposition, [status(thm), theory('equality')], [c_10, c_211])).
% 12.84/6.29  tff(c_557, plain, (![A_9]: (k5_xboole_0(k1_xboole_0, A_9)=k5_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_10, c_485])).
% 12.84/6.29  tff(c_574, plain, (![A_9]: (k5_xboole_0(k1_xboole_0, A_9)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_557])).
% 12.84/6.29  tff(c_287, plain, (![A_9, C_68]: (k5_xboole_0(A_9, k5_xboole_0(A_9, C_68))=k5_xboole_0(k1_xboole_0, C_68))), inference(superposition, [status(thm), theory('equality')], [c_10, c_211])).
% 12.84/6.29  tff(c_575, plain, (![A_9, C_68]: (k5_xboole_0(A_9, k5_xboole_0(A_9, C_68))=C_68)), inference(demodulation, [status(thm), theory('equality')], [c_574, c_287])).
% 12.84/6.29  tff(c_1582, plain, (![B_122, A_121]: (k5_xboole_0(B_122, k2_xboole_0(A_121, B_122))=k5_xboole_0(A_121, k3_xboole_0(A_121, B_122)))), inference(superposition, [status(thm), theory('equality')], [c_1567, c_575])).
% 12.84/6.29  tff(c_2553, plain, (![B_144, A_145]: (k5_xboole_0(B_144, k2_xboole_0(A_145, B_144))=k4_xboole_0(A_145, B_144))), inference(demodulation, [status(thm), theory('equality')], [c_2, c_1582])).
% 12.84/6.29  tff(c_3975, plain, (![B_169, A_170]: (k5_xboole_0(B_169, k4_xboole_0(A_170, B_169))=k2_xboole_0(A_170, B_169))), inference(superposition, [status(thm), theory('equality')], [c_2553, c_575])).
% 12.84/6.29  tff(c_14, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k4_xboole_0(B_13, A_12))=k2_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_39])).
% 12.84/6.29  tff(c_4019, plain, (![B_169, A_170]: (k2_xboole_0(B_169, A_170)=k2_xboole_0(A_170, B_169))), inference(superposition, [status(thm), theory('equality')], [c_3975, c_14])).
% 12.84/6.29  tff(c_640, plain, (![A_81, C_82]: (k5_xboole_0(A_81, k5_xboole_0(A_81, C_82))=C_82)), inference(demodulation, [status(thm), theory('equality')], [c_574, c_287])).
% 12.84/6.29  tff(c_692, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k2_xboole_0(A_12, B_13))=k4_xboole_0(B_13, A_12))), inference(superposition, [status(thm), theory('equality')], [c_14, c_640])).
% 12.84/6.29  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 12.84/6.29  tff(c_88, plain, (![A_52, B_53]: (k5_xboole_0(A_52, k3_xboole_0(A_52, B_53))=k4_xboole_0(A_52, B_53))), inference(cnfTransformation, [status(thm)], [f_27])).
% 12.84/6.29  tff(c_97, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_88])).
% 12.84/6.29  tff(c_101, plain, (![A_54, B_55]: (k4_xboole_0(A_54, k2_xboole_0(A_54, B_55))=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_10, c_97])).
% 12.84/6.29  tff(c_106, plain, (![A_54, B_55]: (k5_xboole_0(k2_xboole_0(A_54, B_55), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_54, B_55), A_54))), inference(superposition, [status(thm), theory('equality')], [c_101, c_14])).
% 12.84/6.29  tff(c_110, plain, (![A_54, B_55]: (k2_xboole_0(k2_xboole_0(A_54, B_55), A_54)=k2_xboole_0(A_54, B_55))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_106])).
% 12.84/6.29  tff(c_2629, plain, (![A_54, B_55]: (k5_xboole_0(A_54, k2_xboole_0(A_54, B_55))=k4_xboole_0(k2_xboole_0(A_54, B_55), A_54))), inference(superposition, [status(thm), theory('equality')], [c_110, c_2553])).
% 12.84/6.29  tff(c_7880, plain, (![A_214, B_215]: (k4_xboole_0(k2_xboole_0(A_214, B_215), A_214)=k4_xboole_0(B_215, A_214))), inference(demodulation, [status(thm), theory('equality')], [c_692, c_2629])).
% 12.84/6.29  tff(c_7960, plain, (![A_170, B_169]: (k4_xboole_0(k2_xboole_0(A_170, B_169), B_169)=k4_xboole_0(A_170, B_169))), inference(superposition, [status(thm), theory('equality')], [c_4019, c_7880])).
% 12.84/6.29  tff(c_30, plain, (k4_xboole_0(k2_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2')), k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_72])).
% 12.84/6.29  tff(c_30708, plain, (k4_xboole_0('#skF_3', k2_tarski('#skF_1', '#skF_2'))!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_7960, c_30])).
% 12.84/6.29  tff(c_30934, plain, (r2_hidden('#skF_2', '#skF_3') | r2_hidden('#skF_1', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_28, c_30708])).
% 12.84/6.29  tff(c_30938, plain, $false, inference(negUnitSimplification, [status(thm)], [c_34, c_32, c_30934])).
% 12.84/6.29  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 12.84/6.29  
% 12.84/6.29  Inference rules
% 12.84/6.29  ----------------------
% 12.84/6.29  #Ref     : 0
% 12.84/6.29  #Sup     : 7790
% 12.84/6.29  #Fact    : 0
% 12.84/6.29  #Define  : 0
% 12.84/6.29  #Split   : 1
% 12.84/6.29  #Chain   : 0
% 12.84/6.29  #Close   : 0
% 12.84/6.29  
% 12.84/6.29  Ordering : KBO
% 12.84/6.29  
% 12.84/6.29  Simplification rules
% 12.84/6.29  ----------------------
% 12.84/6.29  #Subsume      : 416
% 12.84/6.29  #Demod        : 10457
% 12.84/6.29  #Tautology    : 3470
% 12.84/6.29  #SimpNegUnit  : 1
% 12.84/6.29  #BackRed      : 8
% 12.84/6.29  
% 12.84/6.29  #Partial instantiations: 0
% 12.84/6.29  #Strategies tried      : 1
% 12.84/6.29  
% 12.84/6.29  Timing (in seconds)
% 12.84/6.29  ----------------------
% 12.84/6.29  Preprocessing        : 0.29
% 12.84/6.29  Parsing              : 0.16
% 12.84/6.29  CNF conversion       : 0.02
% 12.84/6.29  Main loop            : 5.19
% 12.84/6.29  Inferencing          : 0.78
% 12.84/6.29  Reduction            : 3.45
% 12.84/6.29  Demodulation         : 3.21
% 12.84/6.29  BG Simplification    : 0.13
% 12.84/6.29  Subsumption          : 0.65
% 12.84/6.29  Abstraction          : 0.21
% 12.84/6.29  MUC search           : 0.00
% 12.84/6.29  Cooper               : 0.00
% 12.84/6.29  Total                : 5.52
% 12.84/6.29  Index Insertion      : 0.00
% 12.84/6.29  Index Deletion       : 0.00
% 12.84/6.29  Index Matching       : 0.00
% 12.84/6.29  BG Taut test         : 0.00
%------------------------------------------------------------------------------

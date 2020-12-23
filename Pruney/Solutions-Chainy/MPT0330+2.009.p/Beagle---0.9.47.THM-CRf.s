%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:54:41 EST 2020

% Result     : Theorem 7.84s
% Output     : CNFRefutation 7.84s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 153 expanded)
%              Number of leaves         :   28 (  63 expanded)
%              Depth                    :   13
%              Number of atoms          :   87 ( 194 expanded)
%              Number of equality atoms :   26 (  76 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k4_xboole_0,type,(
    k4_xboole_0: ( $i * $i ) > $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

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

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(f_63,axiom,(
    ! [A,B,C] :
      ( k2_zfmisc_1(k2_xboole_0(A,B),C) = k2_xboole_0(k2_zfmisc_1(A,C),k2_zfmisc_1(B,C))
      & k2_zfmisc_1(C,k2_xboole_0(A,B)) = k2_xboole_0(k2_zfmisc_1(C,A),k2_zfmisc_1(C,B)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t120_zfmisc_1)).

tff(f_70,negated_conjecture,(
    ~ ! [A,B,C,D,E,F] :
        ( ( r1_tarski(A,k2_zfmisc_1(C,D))
          & r1_tarski(B,k2_zfmisc_1(E,F)) )
       => r1_tarski(k2_xboole_0(A,B),k2_zfmisc_1(k2_xboole_0(C,E),k2_xboole_0(D,F))) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t143_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_59,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_xboole_0(B,C))
     => r1_tarski(k4_xboole_0(A,B),C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(B,C) )
     => r1_tarski(A,C) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t1_xboole_1)).

tff(f_51,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k4_xboole_0(A,B),C)
     => r1_tarski(A,k2_xboole_0(B,C)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t44_xboole_1)).

tff(f_37,axiom,(
    ! [A,B,C,D] :
      ( ( r1_tarski(A,B)
        & r1_tarski(C,D) )
     => r1_tarski(k2_xboole_0(A,C),k2_xboole_0(B,D)) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t13_xboole_1)).

tff(c_22,plain,(
    ! [A_26,C_28,B_27] : k2_xboole_0(k2_zfmisc_1(A_26,C_28),k2_zfmisc_1(B_27,C_28)) = k2_zfmisc_1(k2_xboole_0(A_26,B_27),C_28) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_28,plain,(
    r1_tarski('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_65,plain,(
    ! [A_33,B_34] :
      ( k2_xboole_0(A_33,B_34) = B_34
      | ~ r1_tarski(A_33,B_34) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_76,plain,(
    k2_xboole_0('#skF_2',k2_zfmisc_1('#skF_5','#skF_6')) = k2_zfmisc_1('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_28,c_65])).

tff(c_14,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_75,plain,(
    ! [A_18,B_19] : k2_xboole_0(A_18,k2_xboole_0(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(resolution,[status(thm)],[c_14,c_65])).

tff(c_16,plain,(
    ! [B_21,A_20] : k2_tarski(B_21,A_20) = k2_tarski(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_78,plain,(
    ! [A_35,B_36] : k3_tarski(k2_tarski(A_35,B_36)) = k2_xboole_0(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_102,plain,(
    ! [B_39,A_40] : k3_tarski(k2_tarski(B_39,A_40)) = k2_xboole_0(A_40,B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_78])).

tff(c_20,plain,(
    ! [A_24,B_25] : k3_tarski(k2_tarski(A_24,B_25)) = k2_xboole_0(A_24,B_25) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_108,plain,(
    ! [B_39,A_40] : k2_xboole_0(B_39,A_40) = k2_xboole_0(A_40,B_39) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_20])).

tff(c_201,plain,(
    ! [A_50,B_51] : k2_xboole_0(A_50,k2_xboole_0(A_50,B_51)) = k2_xboole_0(A_50,B_51) ),
    inference(resolution,[status(thm)],[c_14,c_65])).

tff(c_225,plain,(
    ! [B_39,A_40] : k2_xboole_0(B_39,k2_xboole_0(A_40,B_39)) = k2_xboole_0(B_39,A_40) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_201])).

tff(c_125,plain,(
    ! [B_41,A_42] : k2_xboole_0(B_41,A_42) = k2_xboole_0(A_42,B_41) ),
    inference(superposition,[status(thm),theory(equality)],[c_102,c_20])).

tff(c_164,plain,(
    ! [A_43,B_44] : r1_tarski(A_43,k2_xboole_0(B_44,A_43)) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_14])).

tff(c_4,plain,(
    ! [A_3,B_4] :
      ( k2_xboole_0(A_3,B_4) = B_4
      | ~ r1_tarski(A_3,B_4) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_601,plain,(
    ! [A_74,B_75] : k2_xboole_0(A_74,k2_xboole_0(B_75,A_74)) = k2_xboole_0(B_75,A_74) ),
    inference(resolution,[status(thm)],[c_164,c_4])).

tff(c_692,plain,(
    ! [B_76,A_77] : k2_xboole_0(B_76,k2_xboole_0(B_76,A_77)) = k2_xboole_0(A_77,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_108,c_601])).

tff(c_758,plain,(
    ! [A_40,B_39] : k2_xboole_0(k2_xboole_0(A_40,B_39),B_39) = k2_xboole_0(B_39,k2_xboole_0(B_39,A_40)) ),
    inference(superposition,[status(thm),theory(equality)],[c_225,c_692])).

tff(c_795,plain,(
    ! [A_40,B_39] : k2_xboole_0(k2_xboole_0(A_40,B_39),B_39) = k2_xboole_0(B_39,A_40) ),
    inference(demodulation,[status(thm),theory(equality)],[c_75,c_758])).

tff(c_140,plain,(
    ! [A_42,B_41] : r1_tarski(A_42,k2_xboole_0(B_41,A_42)) ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_14])).

tff(c_333,plain,(
    ! [A_56,B_57,C_58] :
      ( r1_tarski(k4_xboole_0(A_56,B_57),C_58)
      | ~ r1_tarski(A_56,k2_xboole_0(B_57,C_58)) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_2080,plain,(
    ! [A_123,B_124,C_125] :
      ( k2_xboole_0(k4_xboole_0(A_123,B_124),C_125) = C_125
      | ~ r1_tarski(A_123,k2_xboole_0(B_124,C_125)) ) ),
    inference(resolution,[status(thm)],[c_333,c_4])).

tff(c_2964,plain,(
    ! [A_141,B_142] : k2_xboole_0(k4_xboole_0(A_141,B_142),A_141) = A_141 ),
    inference(resolution,[status(thm)],[c_140,c_2080])).

tff(c_3056,plain,(
    ! [A_141,B_142] : r1_tarski(k4_xboole_0(A_141,B_142),A_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_2964,c_14])).

tff(c_188,plain,(
    ! [A_47,C_48,B_49] :
      ( r1_tarski(A_47,C_48)
      | ~ r1_tarski(B_49,C_48)
      | ~ r1_tarski(A_47,B_49) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_198,plain,(
    ! [A_47,A_18,B_19] :
      ( r1_tarski(A_47,k2_xboole_0(A_18,B_19))
      | ~ r1_tarski(A_47,A_18) ) ),
    inference(resolution,[status(thm)],[c_14,c_188])).

tff(c_4536,plain,(
    ! [A_182,A_183,B_184] :
      ( r1_tarski(A_182,A_183)
      | ~ r1_tarski(A_182,k4_xboole_0(A_183,B_184)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2964,c_198])).

tff(c_4579,plain,(
    ! [A_185,B_186,B_187] : r1_tarski(k4_xboole_0(k4_xboole_0(A_185,B_186),B_187),A_185) ),
    inference(resolution,[status(thm)],[c_3056,c_4536])).

tff(c_12,plain,(
    ! [A_15,B_16,C_17] :
      ( r1_tarski(A_15,k2_xboole_0(B_16,C_17))
      | ~ r1_tarski(k4_xboole_0(A_15,B_16),C_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_4645,plain,(
    ! [A_188,B_189,B_190] : r1_tarski(k4_xboole_0(A_188,B_189),k2_xboole_0(B_190,A_188)) ),
    inference(resolution,[status(thm)],[c_4579,c_12])).

tff(c_4916,plain,(
    ! [B_194,B_195,A_196] : r1_tarski(k4_xboole_0(B_194,B_195),k2_xboole_0(B_194,A_196)) ),
    inference(superposition,[status(thm),theory(equality)],[c_795,c_4645])).

tff(c_7731,plain,(
    ! [B_246,B_247,A_248] : r1_tarski(B_246,k2_xboole_0(B_247,k2_xboole_0(B_246,A_248))) ),
    inference(resolution,[status(thm)],[c_4916,c_12])).

tff(c_8115,plain,(
    ! [B_255] : r1_tarski('#skF_2',k2_xboole_0(B_255,k2_zfmisc_1('#skF_5','#skF_6'))) ),
    inference(superposition,[status(thm),theory(equality)],[c_76,c_7731])).

tff(c_8151,plain,(
    ! [A_26] : r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0(A_26,'#skF_5'),'#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_8115])).

tff(c_30,plain,(
    r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1171,plain,(
    ! [A_88,C_89,B_90] : k2_xboole_0(k2_zfmisc_1(A_88,C_89),k2_zfmisc_1(B_90,C_89)) = k2_zfmisc_1(k2_xboole_0(A_88,B_90),C_89) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1329,plain,(
    ! [A_97,C_98,B_99] : r1_tarski(k2_zfmisc_1(A_97,C_98),k2_zfmisc_1(k2_xboole_0(A_97,B_99),C_98)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1171,c_14])).

tff(c_8,plain,(
    ! [A_9,C_11,B_10] :
      ( r1_tarski(A_9,C_11)
      | ~ r1_tarski(B_10,C_11)
      | ~ r1_tarski(A_9,B_10) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_7448,plain,(
    ! [A_239,A_240,B_241,C_242] :
      ( r1_tarski(A_239,k2_zfmisc_1(k2_xboole_0(A_240,B_241),C_242))
      | ~ r1_tarski(A_239,k2_zfmisc_1(A_240,C_242)) ) ),
    inference(resolution,[status(thm)],[c_1329,c_8])).

tff(c_24,plain,(
    ! [C_28,A_26,B_27] : k2_xboole_0(k2_zfmisc_1(C_28,A_26),k2_zfmisc_1(C_28,B_27)) = k2_zfmisc_1(C_28,k2_xboole_0(A_26,B_27)) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1462,plain,(
    ! [A_106,C_107,B_108,D_109] :
      ( r1_tarski(k2_xboole_0(A_106,C_107),k2_xboole_0(B_108,D_109))
      | ~ r1_tarski(C_107,D_109)
      | ~ r1_tarski(A_106,B_108) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_5030,plain,(
    ! [C_200,C_199,A_198,B_197,A_201] :
      ( r1_tarski(k2_xboole_0(A_201,C_199),k2_zfmisc_1(C_200,k2_xboole_0(A_198,B_197)))
      | ~ r1_tarski(C_199,k2_zfmisc_1(C_200,B_197))
      | ~ r1_tarski(A_201,k2_zfmisc_1(C_200,A_198)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1462])).

tff(c_26,plain,(
    ~ r1_tarski(k2_xboole_0('#skF_1','#skF_2'),k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),k2_xboole_0('#skF_4','#skF_6'))) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_5172,plain,
    ( ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_6'))
    | ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_4')) ),
    inference(resolution,[status(thm)],[c_5030,c_26])).

tff(c_5245,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_4')) ),
    inference(splitLeft,[status(thm)],[c_5172])).

tff(c_7456,plain,(
    ~ r1_tarski('#skF_1',k2_zfmisc_1('#skF_3','#skF_4')) ),
    inference(resolution,[status(thm)],[c_7448,c_5245])).

tff(c_7547,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_7456])).

tff(c_7548,plain,(
    ~ r1_tarski('#skF_2',k2_zfmisc_1(k2_xboole_0('#skF_3','#skF_5'),'#skF_6')) ),
    inference(splitRight,[status(thm)],[c_5172])).

tff(c_9045,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_8151,c_7548])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n018.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 15:03:57 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.84/2.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.84/2.71  
% 7.84/2.71  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.84/2.71  %$ r1_tarski > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_zfmisc_1 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > #skF_5 > #skF_6 > #skF_2 > #skF_3 > #skF_1 > #skF_4
% 7.84/2.71  
% 7.84/2.71  %Foreground sorts:
% 7.84/2.71  
% 7.84/2.71  
% 7.84/2.71  %Background operators:
% 7.84/2.71  
% 7.84/2.71  
% 7.84/2.71  %Foreground operators:
% 7.84/2.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.84/2.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.84/2.71  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.84/2.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.84/2.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.84/2.71  tff('#skF_5', type, '#skF_5': $i).
% 7.84/2.71  tff('#skF_6', type, '#skF_6': $i).
% 7.84/2.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.84/2.71  tff('#skF_2', type, '#skF_2': $i).
% 7.84/2.71  tff('#skF_3', type, '#skF_3': $i).
% 7.84/2.71  tff('#skF_1', type, '#skF_1': $i).
% 7.84/2.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.84/2.71  tff(k3_tarski, type, k3_tarski: $i > $i).
% 7.84/2.71  tff(k2_zfmisc_1, type, k2_zfmisc_1: ($i * $i) > $i).
% 7.84/2.71  tff('#skF_4', type, '#skF_4': $i).
% 7.84/2.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.84/2.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.84/2.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.84/2.71  
% 7.84/2.73  tff(f_63, axiom, (![A, B, C]: ((k2_zfmisc_1(k2_xboole_0(A, B), C) = k2_xboole_0(k2_zfmisc_1(A, C), k2_zfmisc_1(B, C))) & (k2_zfmisc_1(C, k2_xboole_0(A, B)) = k2_xboole_0(k2_zfmisc_1(C, A), k2_zfmisc_1(C, B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t120_zfmisc_1)).
% 7.84/2.73  tff(f_70, negated_conjecture, ~(![A, B, C, D, E, F]: ((r1_tarski(A, k2_zfmisc_1(C, D)) & r1_tarski(B, k2_zfmisc_1(E, F))) => r1_tarski(k2_xboole_0(A, B), k2_zfmisc_1(k2_xboole_0(C, E), k2_xboole_0(D, F))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t143_zfmisc_1)).
% 7.84/2.73  tff(f_31, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 7.84/2.73  tff(f_53, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 7.84/2.73  tff(f_55, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 7.84/2.73  tff(f_59, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 7.84/2.73  tff(f_47, axiom, (![A, B, C]: (r1_tarski(A, k2_xboole_0(B, C)) => r1_tarski(k4_xboole_0(A, B), C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_xboole_1)).
% 7.84/2.73  tff(f_43, axiom, (![A, B, C]: ((r1_tarski(A, B) & r1_tarski(B, C)) => r1_tarski(A, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t1_xboole_1)).
% 7.84/2.73  tff(f_51, axiom, (![A, B, C]: (r1_tarski(k4_xboole_0(A, B), C) => r1_tarski(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t44_xboole_1)).
% 7.84/2.73  tff(f_37, axiom, (![A, B, C, D]: ((r1_tarski(A, B) & r1_tarski(C, D)) => r1_tarski(k2_xboole_0(A, C), k2_xboole_0(B, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t13_xboole_1)).
% 7.84/2.73  tff(c_22, plain, (![A_26, C_28, B_27]: (k2_xboole_0(k2_zfmisc_1(A_26, C_28), k2_zfmisc_1(B_27, C_28))=k2_zfmisc_1(k2_xboole_0(A_26, B_27), C_28))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.84/2.73  tff(c_28, plain, (r1_tarski('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.84/2.73  tff(c_65, plain, (![A_33, B_34]: (k2_xboole_0(A_33, B_34)=B_34 | ~r1_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.84/2.73  tff(c_76, plain, (k2_xboole_0('#skF_2', k2_zfmisc_1('#skF_5', '#skF_6'))=k2_zfmisc_1('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_28, c_65])).
% 7.84/2.73  tff(c_14, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 7.84/2.73  tff(c_75, plain, (![A_18, B_19]: (k2_xboole_0(A_18, k2_xboole_0(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(resolution, [status(thm)], [c_14, c_65])).
% 7.84/2.73  tff(c_16, plain, (![B_21, A_20]: (k2_tarski(B_21, A_20)=k2_tarski(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_55])).
% 7.84/2.73  tff(c_78, plain, (![A_35, B_36]: (k3_tarski(k2_tarski(A_35, B_36))=k2_xboole_0(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.84/2.73  tff(c_102, plain, (![B_39, A_40]: (k3_tarski(k2_tarski(B_39, A_40))=k2_xboole_0(A_40, B_39))), inference(superposition, [status(thm), theory('equality')], [c_16, c_78])).
% 7.84/2.73  tff(c_20, plain, (![A_24, B_25]: (k3_tarski(k2_tarski(A_24, B_25))=k2_xboole_0(A_24, B_25))), inference(cnfTransformation, [status(thm)], [f_59])).
% 7.84/2.73  tff(c_108, plain, (![B_39, A_40]: (k2_xboole_0(B_39, A_40)=k2_xboole_0(A_40, B_39))), inference(superposition, [status(thm), theory('equality')], [c_102, c_20])).
% 7.84/2.73  tff(c_201, plain, (![A_50, B_51]: (k2_xboole_0(A_50, k2_xboole_0(A_50, B_51))=k2_xboole_0(A_50, B_51))), inference(resolution, [status(thm)], [c_14, c_65])).
% 7.84/2.73  tff(c_225, plain, (![B_39, A_40]: (k2_xboole_0(B_39, k2_xboole_0(A_40, B_39))=k2_xboole_0(B_39, A_40))), inference(superposition, [status(thm), theory('equality')], [c_108, c_201])).
% 7.84/2.73  tff(c_125, plain, (![B_41, A_42]: (k2_xboole_0(B_41, A_42)=k2_xboole_0(A_42, B_41))), inference(superposition, [status(thm), theory('equality')], [c_102, c_20])).
% 7.84/2.73  tff(c_164, plain, (![A_43, B_44]: (r1_tarski(A_43, k2_xboole_0(B_44, A_43)))), inference(superposition, [status(thm), theory('equality')], [c_125, c_14])).
% 7.84/2.73  tff(c_4, plain, (![A_3, B_4]: (k2_xboole_0(A_3, B_4)=B_4 | ~r1_tarski(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.84/2.73  tff(c_601, plain, (![A_74, B_75]: (k2_xboole_0(A_74, k2_xboole_0(B_75, A_74))=k2_xboole_0(B_75, A_74))), inference(resolution, [status(thm)], [c_164, c_4])).
% 7.84/2.73  tff(c_692, plain, (![B_76, A_77]: (k2_xboole_0(B_76, k2_xboole_0(B_76, A_77))=k2_xboole_0(A_77, B_76))), inference(superposition, [status(thm), theory('equality')], [c_108, c_601])).
% 7.84/2.73  tff(c_758, plain, (![A_40, B_39]: (k2_xboole_0(k2_xboole_0(A_40, B_39), B_39)=k2_xboole_0(B_39, k2_xboole_0(B_39, A_40)))), inference(superposition, [status(thm), theory('equality')], [c_225, c_692])).
% 7.84/2.73  tff(c_795, plain, (![A_40, B_39]: (k2_xboole_0(k2_xboole_0(A_40, B_39), B_39)=k2_xboole_0(B_39, A_40))), inference(demodulation, [status(thm), theory('equality')], [c_75, c_758])).
% 7.84/2.73  tff(c_140, plain, (![A_42, B_41]: (r1_tarski(A_42, k2_xboole_0(B_41, A_42)))), inference(superposition, [status(thm), theory('equality')], [c_125, c_14])).
% 7.84/2.73  tff(c_333, plain, (![A_56, B_57, C_58]: (r1_tarski(k4_xboole_0(A_56, B_57), C_58) | ~r1_tarski(A_56, k2_xboole_0(B_57, C_58)))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.84/2.73  tff(c_2080, plain, (![A_123, B_124, C_125]: (k2_xboole_0(k4_xboole_0(A_123, B_124), C_125)=C_125 | ~r1_tarski(A_123, k2_xboole_0(B_124, C_125)))), inference(resolution, [status(thm)], [c_333, c_4])).
% 7.84/2.73  tff(c_2964, plain, (![A_141, B_142]: (k2_xboole_0(k4_xboole_0(A_141, B_142), A_141)=A_141)), inference(resolution, [status(thm)], [c_140, c_2080])).
% 7.84/2.73  tff(c_3056, plain, (![A_141, B_142]: (r1_tarski(k4_xboole_0(A_141, B_142), A_141))), inference(superposition, [status(thm), theory('equality')], [c_2964, c_14])).
% 7.84/2.73  tff(c_188, plain, (![A_47, C_48, B_49]: (r1_tarski(A_47, C_48) | ~r1_tarski(B_49, C_48) | ~r1_tarski(A_47, B_49))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.84/2.73  tff(c_198, plain, (![A_47, A_18, B_19]: (r1_tarski(A_47, k2_xboole_0(A_18, B_19)) | ~r1_tarski(A_47, A_18))), inference(resolution, [status(thm)], [c_14, c_188])).
% 7.84/2.73  tff(c_4536, plain, (![A_182, A_183, B_184]: (r1_tarski(A_182, A_183) | ~r1_tarski(A_182, k4_xboole_0(A_183, B_184)))), inference(superposition, [status(thm), theory('equality')], [c_2964, c_198])).
% 7.84/2.73  tff(c_4579, plain, (![A_185, B_186, B_187]: (r1_tarski(k4_xboole_0(k4_xboole_0(A_185, B_186), B_187), A_185))), inference(resolution, [status(thm)], [c_3056, c_4536])).
% 7.84/2.73  tff(c_12, plain, (![A_15, B_16, C_17]: (r1_tarski(A_15, k2_xboole_0(B_16, C_17)) | ~r1_tarski(k4_xboole_0(A_15, B_16), C_17))), inference(cnfTransformation, [status(thm)], [f_51])).
% 7.84/2.73  tff(c_4645, plain, (![A_188, B_189, B_190]: (r1_tarski(k4_xboole_0(A_188, B_189), k2_xboole_0(B_190, A_188)))), inference(resolution, [status(thm)], [c_4579, c_12])).
% 7.84/2.73  tff(c_4916, plain, (![B_194, B_195, A_196]: (r1_tarski(k4_xboole_0(B_194, B_195), k2_xboole_0(B_194, A_196)))), inference(superposition, [status(thm), theory('equality')], [c_795, c_4645])).
% 7.84/2.73  tff(c_7731, plain, (![B_246, B_247, A_248]: (r1_tarski(B_246, k2_xboole_0(B_247, k2_xboole_0(B_246, A_248))))), inference(resolution, [status(thm)], [c_4916, c_12])).
% 7.84/2.73  tff(c_8115, plain, (![B_255]: (r1_tarski('#skF_2', k2_xboole_0(B_255, k2_zfmisc_1('#skF_5', '#skF_6'))))), inference(superposition, [status(thm), theory('equality')], [c_76, c_7731])).
% 7.84/2.73  tff(c_8151, plain, (![A_26]: (r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0(A_26, '#skF_5'), '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_22, c_8115])).
% 7.84/2.73  tff(c_30, plain, (r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.84/2.73  tff(c_1171, plain, (![A_88, C_89, B_90]: (k2_xboole_0(k2_zfmisc_1(A_88, C_89), k2_zfmisc_1(B_90, C_89))=k2_zfmisc_1(k2_xboole_0(A_88, B_90), C_89))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.84/2.73  tff(c_1329, plain, (![A_97, C_98, B_99]: (r1_tarski(k2_zfmisc_1(A_97, C_98), k2_zfmisc_1(k2_xboole_0(A_97, B_99), C_98)))), inference(superposition, [status(thm), theory('equality')], [c_1171, c_14])).
% 7.84/2.73  tff(c_8, plain, (![A_9, C_11, B_10]: (r1_tarski(A_9, C_11) | ~r1_tarski(B_10, C_11) | ~r1_tarski(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.84/2.73  tff(c_7448, plain, (![A_239, A_240, B_241, C_242]: (r1_tarski(A_239, k2_zfmisc_1(k2_xboole_0(A_240, B_241), C_242)) | ~r1_tarski(A_239, k2_zfmisc_1(A_240, C_242)))), inference(resolution, [status(thm)], [c_1329, c_8])).
% 7.84/2.73  tff(c_24, plain, (![C_28, A_26, B_27]: (k2_xboole_0(k2_zfmisc_1(C_28, A_26), k2_zfmisc_1(C_28, B_27))=k2_zfmisc_1(C_28, k2_xboole_0(A_26, B_27)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 7.84/2.73  tff(c_1462, plain, (![A_106, C_107, B_108, D_109]: (r1_tarski(k2_xboole_0(A_106, C_107), k2_xboole_0(B_108, D_109)) | ~r1_tarski(C_107, D_109) | ~r1_tarski(A_106, B_108))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.84/2.73  tff(c_5030, plain, (![C_200, C_199, A_198, B_197, A_201]: (r1_tarski(k2_xboole_0(A_201, C_199), k2_zfmisc_1(C_200, k2_xboole_0(A_198, B_197))) | ~r1_tarski(C_199, k2_zfmisc_1(C_200, B_197)) | ~r1_tarski(A_201, k2_zfmisc_1(C_200, A_198)))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1462])).
% 7.84/2.73  tff(c_26, plain, (~r1_tarski(k2_xboole_0('#skF_1', '#skF_2'), k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), k2_xboole_0('#skF_4', '#skF_6')))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.84/2.73  tff(c_5172, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_6')) | ~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4'))), inference(resolution, [status(thm)], [c_5030, c_26])).
% 7.84/2.73  tff(c_5245, plain, (~r1_tarski('#skF_1', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_4'))), inference(splitLeft, [status(thm)], [c_5172])).
% 7.84/2.73  tff(c_7456, plain, (~r1_tarski('#skF_1', k2_zfmisc_1('#skF_3', '#skF_4'))), inference(resolution, [status(thm)], [c_7448, c_5245])).
% 7.84/2.73  tff(c_7547, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_30, c_7456])).
% 7.84/2.73  tff(c_7548, plain, (~r1_tarski('#skF_2', k2_zfmisc_1(k2_xboole_0('#skF_3', '#skF_5'), '#skF_6'))), inference(splitRight, [status(thm)], [c_5172])).
% 7.84/2.73  tff(c_9045, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_8151, c_7548])).
% 7.84/2.73  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.84/2.73  
% 7.84/2.73  Inference rules
% 7.84/2.73  ----------------------
% 7.84/2.73  #Ref     : 0
% 7.84/2.73  #Sup     : 2359
% 7.84/2.73  #Fact    : 0
% 7.84/2.73  #Define  : 0
% 7.84/2.73  #Split   : 4
% 7.84/2.73  #Chain   : 0
% 7.84/2.73  #Close   : 0
% 7.84/2.73  
% 7.84/2.73  Ordering : KBO
% 7.84/2.73  
% 7.84/2.73  Simplification rules
% 7.84/2.73  ----------------------
% 7.84/2.73  #Subsume      : 220
% 7.84/2.73  #Demod        : 1077
% 7.84/2.73  #Tautology    : 954
% 7.84/2.73  #SimpNegUnit  : 0
% 7.84/2.73  #BackRed      : 2
% 7.84/2.73  
% 7.84/2.73  #Partial instantiations: 0
% 7.84/2.73  #Strategies tried      : 1
% 7.84/2.73  
% 7.84/2.73  Timing (in seconds)
% 7.84/2.73  ----------------------
% 7.84/2.73  Preprocessing        : 0.32
% 7.84/2.73  Parsing              : 0.18
% 7.84/2.73  CNF conversion       : 0.02
% 7.84/2.73  Main loop            : 1.64
% 7.84/2.73  Inferencing          : 0.43
% 7.84/2.73  Reduction            : 0.74
% 7.84/2.73  Demodulation         : 0.62
% 7.84/2.73  BG Simplification    : 0.05
% 7.84/2.73  Subsumption          : 0.32
% 7.84/2.73  Abstraction          : 0.07
% 7.84/2.73  MUC search           : 0.00
% 7.84/2.73  Cooper               : 0.00
% 7.84/2.73  Total                : 2.00
% 7.84/2.73  Index Insertion      : 0.00
% 7.84/2.73  Index Deletion       : 0.00
% 7.84/2.73  Index Matching       : 0.00
% 7.84/2.73  BG Taut test         : 0.00
%------------------------------------------------------------------------------

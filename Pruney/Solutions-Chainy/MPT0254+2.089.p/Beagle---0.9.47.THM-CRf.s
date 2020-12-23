%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n018.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:30 EST 2020

% Result     : Theorem 5.90s
% Output     : CNFRefutation 6.28s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 154 expanded)
%              Number of leaves         :   41 (  69 expanded)
%              Depth                    :   12
%              Number of atoms          :   79 ( 140 expanded)
%              Number of equality atoms :   56 ( 117 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1

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

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_53,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_45,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_100,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_47,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_61,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_65,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_82,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_84,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_22,plain,(
    ! [A_20] : k5_xboole_0(A_20,k1_xboole_0) = A_20 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_16,plain,(
    ! [A_16] : k3_xboole_0(A_16,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_312,plain,(
    ! [A_88,B_89] : r1_xboole_0(k3_xboole_0(A_88,B_89),k5_xboole_0(A_88,B_89)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_333,plain,(
    ! [A_16] : r1_xboole_0(k1_xboole_0,k5_xboole_0(A_16,k1_xboole_0)) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_312])).

tff(c_342,plain,(
    ! [A_16] : r1_xboole_0(k1_xboole_0,A_16) ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_333])).

tff(c_120,plain,(
    ! [B_74,A_75] : k3_xboole_0(B_74,A_75) = k3_xboole_0(A_75,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_136,plain,(
    ! [A_75] : k3_xboole_0(k1_xboole_0,A_75) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_120,c_16])).

tff(c_530,plain,(
    ! [A_109,B_110,C_111] :
      ( ~ r1_xboole_0(A_109,B_110)
      | ~ r2_hidden(C_111,k3_xboole_0(A_109,B_110)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_533,plain,(
    ! [A_75,C_111] :
      ( ~ r1_xboole_0(k1_xboole_0,A_75)
      | ~ r2_hidden(C_111,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_530])).

tff(c_544,plain,(
    ! [C_111] : ~ r2_hidden(C_111,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_342,c_533])).

tff(c_70,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_452,plain,(
    ! [A_104,B_105] : k5_xboole_0(A_104,k3_xboole_0(A_104,B_105)) = k4_xboole_0(A_104,B_105) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_478,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_452])).

tff(c_4,plain,(
    ! [B_4,A_3] : k5_xboole_0(B_4,A_3) = k5_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_24,plain,(
    ! [A_21,B_22,C_23] : k5_xboole_0(k5_xboole_0(A_21,B_22),C_23) = k5_xboole_0(A_21,k5_xboole_0(B_22,C_23)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1129,plain,(
    ! [A_132,B_133] : k5_xboole_0(k5_xboole_0(A_132,B_133),k3_xboole_0(A_132,B_133)) = k2_xboole_0(A_132,B_133) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_1190,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k5_xboole_0(B_22,k3_xboole_0(A_21,B_22))) = k2_xboole_0(A_21,B_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_1129])).

tff(c_5977,plain,(
    ! [A_15181,B_15182] : k5_xboole_0(A_15181,k4_xboole_0(B_15182,A_15181)) = k2_xboole_0(A_15181,B_15182) ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_1190])).

tff(c_204,plain,(
    ! [B_80,A_81] : k5_xboole_0(B_80,A_81) = k5_xboole_0(A_81,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_220,plain,(
    ! [A_81] : k5_xboole_0(k1_xboole_0,A_81) = A_81 ),
    inference(superposition,[status(thm),theory(equality)],[c_204,c_22])).

tff(c_26,plain,(
    ! [A_24] : k5_xboole_0(A_24,A_24) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_634,plain,(
    ! [A_119,B_120,C_121] : k5_xboole_0(k5_xboole_0(A_119,B_120),C_121) = k5_xboole_0(A_119,k5_xboole_0(B_120,C_121)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_704,plain,(
    ! [A_24,C_121] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_121)) = k5_xboole_0(k1_xboole_0,C_121) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_634])).

tff(c_717,plain,(
    ! [A_24,C_121] : k5_xboole_0(A_24,k5_xboole_0(A_24,C_121)) = C_121 ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_704])).

tff(c_6294,plain,(
    ! [A_15682,B_15683] : k5_xboole_0(A_15682,k2_xboole_0(A_15682,B_15683)) = k4_xboole_0(B_15683,A_15682) ),
    inference(superposition,[status(thm),theory(equality)],[c_5977,c_717])).

tff(c_6397,plain,(
    k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) = k4_xboole_0('#skF_5',k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_6294])).

tff(c_6412,plain,(
    k4_xboole_0('#skF_5',k1_tarski('#skF_4')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_22,c_6397])).

tff(c_1641,plain,(
    ! [A_184,B_185] : k5_xboole_0(A_184,k3_xboole_0(B_185,A_184)) = k4_xboole_0(A_184,B_185) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_452])).

tff(c_720,plain,(
    ! [A_122,C_123] : k5_xboole_0(A_122,k5_xboole_0(A_122,C_123)) = C_123 ),
    inference(demodulation,[status(thm),theory(equality)],[c_220,c_704])).

tff(c_769,plain,(
    ! [A_3,B_4] : k5_xboole_0(A_3,k5_xboole_0(B_4,A_3)) = B_4 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_720])).

tff(c_1662,plain,(
    ! [B_185,A_184] : k5_xboole_0(k3_xboole_0(B_185,A_184),k4_xboole_0(A_184,B_185)) = A_184 ),
    inference(superposition,[status(thm),theory(equality)],[c_1641,c_769])).

tff(c_6425,plain,(
    k5_xboole_0(k3_xboole_0(k1_tarski('#skF_4'),'#skF_5'),k1_tarski('#skF_4')) = '#skF_5' ),
    inference(superposition,[status(thm),theory(equality)],[c_6412,c_1662])).

tff(c_6472,plain,(
    k4_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_478,c_4,c_2,c_6425])).

tff(c_792,plain,(
    ! [A_124,B_125] : k5_xboole_0(A_124,k5_xboole_0(B_125,A_124)) = B_125 ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_720])).

tff(c_831,plain,(
    ! [A_24,C_121] : k5_xboole_0(k5_xboole_0(A_24,C_121),C_121) = A_24 ),
    inference(superposition,[status(thm),theory(equality)],[c_717,c_792])).

tff(c_20,plain,(
    ! [A_18,B_19] : r1_tarski(k4_xboole_0(A_18,B_19),A_18) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_301,plain,(
    ! [A_86,B_87] :
      ( k3_xboole_0(A_86,B_87) = A_86
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_1492,plain,(
    ! [A_174,B_175] : k3_xboole_0(k4_xboole_0(A_174,B_175),A_174) = k4_xboole_0(A_174,B_175) ),
    inference(resolution,[status(thm)],[c_20,c_301])).

tff(c_4734,plain,(
    ! [A_12342,B_12343] : k3_xboole_0(A_12342,k4_xboole_0(A_12342,B_12343)) = k4_xboole_0(A_12342,B_12343) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1492])).

tff(c_28,plain,(
    ! [A_25,B_26] : k5_xboole_0(k5_xboole_0(A_25,B_26),k3_xboole_0(A_25,B_26)) = k2_xboole_0(A_25,B_26) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_4752,plain,(
    ! [A_12342,B_12343] : k5_xboole_0(k5_xboole_0(A_12342,k4_xboole_0(A_12342,B_12343)),k4_xboole_0(A_12342,B_12343)) = k2_xboole_0(A_12342,k4_xboole_0(A_12342,B_12343)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4734,c_28])).

tff(c_4801,plain,(
    ! [A_12342,B_12343] : k2_xboole_0(A_12342,k4_xboole_0(A_12342,B_12343)) = A_12342 ),
    inference(demodulation,[status(thm),theory(equality)],[c_831,c_4752])).

tff(c_6513,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_6472,c_4801])).

tff(c_6546,plain,(
    k1_tarski('#skF_4') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_6513])).

tff(c_54,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_347,plain,(
    ! [A_91,B_92] : k1_enumset1(A_91,A_91,B_92) = k2_tarski(A_91,B_92) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_36,plain,(
    ! [E_33,B_28,C_29] : r2_hidden(E_33,k1_enumset1(E_33,B_28,C_29)) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_375,plain,(
    ! [A_94,B_95] : r2_hidden(A_94,k2_tarski(A_94,B_95)) ),
    inference(superposition,[status(thm),theory(equality)],[c_347,c_36])).

tff(c_378,plain,(
    ! [A_34] : r2_hidden(A_34,k1_tarski(A_34)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_375])).

tff(c_6564,plain,(
    r2_hidden('#skF_4',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_6546,c_378])).

tff(c_6568,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_544,c_6564])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.33  % Computer   : n018.cluster.edu
% 0.12/0.33  % Model      : x86_64 x86_64
% 0.12/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.33  % Memory     : 8042.1875MB
% 0.12/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 12:29:41 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.90/2.23  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.90/2.24  
% 5.90/2.24  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 5.90/2.24  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_4 > #skF_3 > #skF_1
% 5.90/2.24  
% 5.90/2.24  %Foreground sorts:
% 5.90/2.24  
% 5.90/2.24  
% 5.90/2.24  %Background operators:
% 5.90/2.24  
% 5.90/2.24  
% 5.90/2.24  %Foreground operators:
% 5.90/2.24  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.90/2.24  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.90/2.24  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.90/2.24  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.90/2.24  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.90/2.24  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.90/2.24  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.90/2.24  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.90/2.24  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.90/2.24  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.90/2.24  tff('#skF_5', type, '#skF_5': $i).
% 5.90/2.24  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.90/2.24  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.90/2.24  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.90/2.24  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.90/2.24  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.90/2.24  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.90/2.24  tff(k3_tarski, type, k3_tarski: $i > $i).
% 5.90/2.24  tff('#skF_4', type, '#skF_4': $i).
% 5.90/2.24  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.90/2.24  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.90/2.24  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 5.90/2.24  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.90/2.24  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.90/2.24  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 5.90/2.24  
% 6.28/2.26  tff(f_59, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 6.28/2.26  tff(f_53, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 6.28/2.26  tff(f_45, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l97_xboole_1)).
% 6.28/2.26  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.28/2.26  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 6.28/2.26  tff(f_100, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 6.28/2.26  tff(f_47, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.28/2.26  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 6.28/2.26  tff(f_61, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 6.28/2.26  tff(f_65, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t94_xboole_1)).
% 6.28/2.26  tff(f_63, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 6.28/2.26  tff(f_57, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 6.28/2.26  tff(f_51, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.28/2.26  tff(f_82, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 6.28/2.26  tff(f_84, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 6.28/2.26  tff(f_80, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 6.28/2.26  tff(c_22, plain, (![A_20]: (k5_xboole_0(A_20, k1_xboole_0)=A_20)), inference(cnfTransformation, [status(thm)], [f_59])).
% 6.28/2.26  tff(c_16, plain, (![A_16]: (k3_xboole_0(A_16, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.28/2.26  tff(c_312, plain, (![A_88, B_89]: (r1_xboole_0(k3_xboole_0(A_88, B_89), k5_xboole_0(A_88, B_89)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 6.28/2.26  tff(c_333, plain, (![A_16]: (r1_xboole_0(k1_xboole_0, k5_xboole_0(A_16, k1_xboole_0)))), inference(superposition, [status(thm), theory('equality')], [c_16, c_312])).
% 6.28/2.26  tff(c_342, plain, (![A_16]: (r1_xboole_0(k1_xboole_0, A_16))), inference(demodulation, [status(thm), theory('equality')], [c_22, c_333])).
% 6.28/2.26  tff(c_120, plain, (![B_74, A_75]: (k3_xboole_0(B_74, A_75)=k3_xboole_0(A_75, B_74))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.28/2.26  tff(c_136, plain, (![A_75]: (k3_xboole_0(k1_xboole_0, A_75)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_120, c_16])).
% 6.28/2.26  tff(c_530, plain, (![A_109, B_110, C_111]: (~r1_xboole_0(A_109, B_110) | ~r2_hidden(C_111, k3_xboole_0(A_109, B_110)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.28/2.26  tff(c_533, plain, (![A_75, C_111]: (~r1_xboole_0(k1_xboole_0, A_75) | ~r2_hidden(C_111, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_136, c_530])).
% 6.28/2.26  tff(c_544, plain, (![C_111]: (~r2_hidden(C_111, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_342, c_533])).
% 6.28/2.26  tff(c_70, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_100])).
% 6.28/2.26  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.28/2.26  tff(c_452, plain, (![A_104, B_105]: (k5_xboole_0(A_104, k3_xboole_0(A_104, B_105))=k4_xboole_0(A_104, B_105))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.28/2.26  tff(c_478, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_452])).
% 6.28/2.26  tff(c_4, plain, (![B_4, A_3]: (k5_xboole_0(B_4, A_3)=k5_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.28/2.26  tff(c_24, plain, (![A_21, B_22, C_23]: (k5_xboole_0(k5_xboole_0(A_21, B_22), C_23)=k5_xboole_0(A_21, k5_xboole_0(B_22, C_23)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.28/2.26  tff(c_1129, plain, (![A_132, B_133]: (k5_xboole_0(k5_xboole_0(A_132, B_133), k3_xboole_0(A_132, B_133))=k2_xboole_0(A_132, B_133))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.28/2.26  tff(c_1190, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k5_xboole_0(B_22, k3_xboole_0(A_21, B_22)))=k2_xboole_0(A_21, B_22))), inference(superposition, [status(thm), theory('equality')], [c_24, c_1129])).
% 6.28/2.26  tff(c_5977, plain, (![A_15181, B_15182]: (k5_xboole_0(A_15181, k4_xboole_0(B_15182, A_15181))=k2_xboole_0(A_15181, B_15182))), inference(demodulation, [status(thm), theory('equality')], [c_478, c_1190])).
% 6.28/2.26  tff(c_204, plain, (![B_80, A_81]: (k5_xboole_0(B_80, A_81)=k5_xboole_0(A_81, B_80))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.28/2.26  tff(c_220, plain, (![A_81]: (k5_xboole_0(k1_xboole_0, A_81)=A_81)), inference(superposition, [status(thm), theory('equality')], [c_204, c_22])).
% 6.28/2.26  tff(c_26, plain, (![A_24]: (k5_xboole_0(A_24, A_24)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_63])).
% 6.28/2.26  tff(c_634, plain, (![A_119, B_120, C_121]: (k5_xboole_0(k5_xboole_0(A_119, B_120), C_121)=k5_xboole_0(A_119, k5_xboole_0(B_120, C_121)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 6.28/2.26  tff(c_704, plain, (![A_24, C_121]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_121))=k5_xboole_0(k1_xboole_0, C_121))), inference(superposition, [status(thm), theory('equality')], [c_26, c_634])).
% 6.28/2.26  tff(c_717, plain, (![A_24, C_121]: (k5_xboole_0(A_24, k5_xboole_0(A_24, C_121))=C_121)), inference(demodulation, [status(thm), theory('equality')], [c_220, c_704])).
% 6.28/2.26  tff(c_6294, plain, (![A_15682, B_15683]: (k5_xboole_0(A_15682, k2_xboole_0(A_15682, B_15683))=k4_xboole_0(B_15683, A_15682))), inference(superposition, [status(thm), theory('equality')], [c_5977, c_717])).
% 6.28/2.26  tff(c_6397, plain, (k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)=k4_xboole_0('#skF_5', k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_70, c_6294])).
% 6.28/2.26  tff(c_6412, plain, (k4_xboole_0('#skF_5', k1_tarski('#skF_4'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_22, c_6397])).
% 6.28/2.26  tff(c_1641, plain, (![A_184, B_185]: (k5_xboole_0(A_184, k3_xboole_0(B_185, A_184))=k4_xboole_0(A_184, B_185))), inference(superposition, [status(thm), theory('equality')], [c_2, c_452])).
% 6.28/2.26  tff(c_720, plain, (![A_122, C_123]: (k5_xboole_0(A_122, k5_xboole_0(A_122, C_123))=C_123)), inference(demodulation, [status(thm), theory('equality')], [c_220, c_704])).
% 6.28/2.26  tff(c_769, plain, (![A_3, B_4]: (k5_xboole_0(A_3, k5_xboole_0(B_4, A_3))=B_4)), inference(superposition, [status(thm), theory('equality')], [c_4, c_720])).
% 6.28/2.26  tff(c_1662, plain, (![B_185, A_184]: (k5_xboole_0(k3_xboole_0(B_185, A_184), k4_xboole_0(A_184, B_185))=A_184)), inference(superposition, [status(thm), theory('equality')], [c_1641, c_769])).
% 6.28/2.26  tff(c_6425, plain, (k5_xboole_0(k3_xboole_0(k1_tarski('#skF_4'), '#skF_5'), k1_tarski('#skF_4'))='#skF_5'), inference(superposition, [status(thm), theory('equality')], [c_6412, c_1662])).
% 6.28/2.26  tff(c_6472, plain, (k4_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_478, c_4, c_2, c_6425])).
% 6.28/2.26  tff(c_792, plain, (![A_124, B_125]: (k5_xboole_0(A_124, k5_xboole_0(B_125, A_124))=B_125)), inference(superposition, [status(thm), theory('equality')], [c_4, c_720])).
% 6.28/2.26  tff(c_831, plain, (![A_24, C_121]: (k5_xboole_0(k5_xboole_0(A_24, C_121), C_121)=A_24)), inference(superposition, [status(thm), theory('equality')], [c_717, c_792])).
% 6.28/2.26  tff(c_20, plain, (![A_18, B_19]: (r1_tarski(k4_xboole_0(A_18, B_19), A_18))), inference(cnfTransformation, [status(thm)], [f_57])).
% 6.28/2.26  tff(c_301, plain, (![A_86, B_87]: (k3_xboole_0(A_86, B_87)=A_86 | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.28/2.26  tff(c_1492, plain, (![A_174, B_175]: (k3_xboole_0(k4_xboole_0(A_174, B_175), A_174)=k4_xboole_0(A_174, B_175))), inference(resolution, [status(thm)], [c_20, c_301])).
% 6.28/2.26  tff(c_4734, plain, (![A_12342, B_12343]: (k3_xboole_0(A_12342, k4_xboole_0(A_12342, B_12343))=k4_xboole_0(A_12342, B_12343))), inference(superposition, [status(thm), theory('equality')], [c_2, c_1492])).
% 6.28/2.26  tff(c_28, plain, (![A_25, B_26]: (k5_xboole_0(k5_xboole_0(A_25, B_26), k3_xboole_0(A_25, B_26))=k2_xboole_0(A_25, B_26))), inference(cnfTransformation, [status(thm)], [f_65])).
% 6.28/2.26  tff(c_4752, plain, (![A_12342, B_12343]: (k5_xboole_0(k5_xboole_0(A_12342, k4_xboole_0(A_12342, B_12343)), k4_xboole_0(A_12342, B_12343))=k2_xboole_0(A_12342, k4_xboole_0(A_12342, B_12343)))), inference(superposition, [status(thm), theory('equality')], [c_4734, c_28])).
% 6.28/2.26  tff(c_4801, plain, (![A_12342, B_12343]: (k2_xboole_0(A_12342, k4_xboole_0(A_12342, B_12343))=A_12342)), inference(demodulation, [status(thm), theory('equality')], [c_831, c_4752])).
% 6.28/2.26  tff(c_6513, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_6472, c_4801])).
% 6.28/2.26  tff(c_6546, plain, (k1_tarski('#skF_4')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_70, c_6513])).
% 6.28/2.26  tff(c_54, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_82])).
% 6.28/2.26  tff(c_347, plain, (![A_91, B_92]: (k1_enumset1(A_91, A_91, B_92)=k2_tarski(A_91, B_92))), inference(cnfTransformation, [status(thm)], [f_84])).
% 6.28/2.26  tff(c_36, plain, (![E_33, B_28, C_29]: (r2_hidden(E_33, k1_enumset1(E_33, B_28, C_29)))), inference(cnfTransformation, [status(thm)], [f_80])).
% 6.28/2.26  tff(c_375, plain, (![A_94, B_95]: (r2_hidden(A_94, k2_tarski(A_94, B_95)))), inference(superposition, [status(thm), theory('equality')], [c_347, c_36])).
% 6.28/2.26  tff(c_378, plain, (![A_34]: (r2_hidden(A_34, k1_tarski(A_34)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_375])).
% 6.28/2.26  tff(c_6564, plain, (r2_hidden('#skF_4', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_6546, c_378])).
% 6.28/2.26  tff(c_6568, plain, $false, inference(negUnitSimplification, [status(thm)], [c_544, c_6564])).
% 6.28/2.26  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 6.28/2.26  
% 6.28/2.26  Inference rules
% 6.28/2.26  ----------------------
% 6.28/2.26  #Ref     : 0
% 6.28/2.26  #Sup     : 1198
% 6.28/2.26  #Fact    : 18
% 6.28/2.26  #Define  : 0
% 6.28/2.26  #Split   : 0
% 6.28/2.26  #Chain   : 0
% 6.28/2.26  #Close   : 0
% 6.28/2.26  
% 6.28/2.26  Ordering : KBO
% 6.28/2.26  
% 6.28/2.26  Simplification rules
% 6.28/2.26  ----------------------
% 6.28/2.26  #Subsume      : 87
% 6.28/2.26  #Demod        : 821
% 6.28/2.26  #Tautology    : 660
% 6.28/2.26  #SimpNegUnit  : 12
% 6.28/2.26  #BackRed      : 6
% 6.28/2.26  
% 6.28/2.26  #Partial instantiations: 5586
% 6.28/2.26  #Strategies tried      : 1
% 6.28/2.26  
% 6.28/2.26  Timing (in seconds)
% 6.28/2.26  ----------------------
% 6.28/2.26  Preprocessing        : 0.35
% 6.28/2.26  Parsing              : 0.18
% 6.28/2.26  CNF conversion       : 0.02
% 6.28/2.26  Main loop            : 1.12
% 6.28/2.26  Inferencing          : 0.54
% 6.28/2.26  Reduction            : 0.35
% 6.28/2.26  Demodulation         : 0.29
% 6.28/2.26  BG Simplification    : 0.04
% 6.28/2.26  Subsumption          : 0.13
% 6.28/2.26  Abstraction          : 0.05
% 6.28/2.26  MUC search           : 0.00
% 6.28/2.26  Cooper               : 0.00
% 6.28/2.26  Total                : 1.50
% 6.28/2.26  Index Insertion      : 0.00
% 6.28/2.26  Index Deletion       : 0.00
% 6.28/2.26  Index Matching       : 0.00
% 6.28/2.26  BG Taut test         : 0.00
%------------------------------------------------------------------------------

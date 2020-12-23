%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:35 EST 2020

% Result     : Theorem 3.39s
% Output     : CNFRefutation 3.56s
% Verified   : 
% Statistics : Number of formulae       :   82 ( 198 expanded)
%              Number of leaves         :   39 (  83 expanded)
%              Depth                    :   18
%              Number of atoms          :   79 ( 229 expanded)
%              Number of equality atoms :   53 ( 171 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(v1_xboole_0,type,(
    v1_xboole_0: $i > $o )).

tff(f_91,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_76,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_74,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_72,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( ~ v1_xboole_0(B)
     => ~ ( r1_tarski(B,A)
          & r1_xboole_0(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_xboole_1)).

tff(f_31,axiom,(
    ! [A] :
      ( v1_xboole_0(A)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l13_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_62,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_50,plain,(
    ! [A_32,B_33] : k1_enumset1(A_32,A_32,B_33) = k2_tarski(A_32,B_33) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_48,plain,(
    ! [A_31] : k2_tarski(A_31,A_31) = k1_tarski(A_31) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_52,plain,(
    ! [A_34,B_35,C_36] : k2_enumset1(A_34,A_34,B_35,C_36) = k1_enumset1(A_34,B_35,C_36) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_527,plain,(
    ! [A_106,B_107,C_108,D_109] : k2_xboole_0(k1_enumset1(A_106,B_107,C_108),k1_tarski(D_109)) = k2_enumset1(A_106,B_107,C_108,D_109) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_545,plain,(
    ! [A_32,B_33,D_109] : k2_xboole_0(k2_tarski(A_32,B_33),k1_tarski(D_109)) = k2_enumset1(A_32,A_32,B_33,D_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_527])).

tff(c_778,plain,(
    ! [A_130,B_131,D_132] : k2_xboole_0(k2_tarski(A_130,B_131),k1_tarski(D_132)) = k1_enumset1(A_130,B_131,D_132) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_545])).

tff(c_787,plain,(
    ! [A_31,D_132] : k2_xboole_0(k1_tarski(A_31),k1_tarski(D_132)) = k1_enumset1(A_31,A_31,D_132) ),
    inference(superposition,[status(thm),theory(equality)],[c_48,c_778])).

tff(c_790,plain,(
    ! [A_31,D_132] : k2_xboole_0(k1_tarski(A_31),k1_tarski(D_132)) = k2_tarski(A_31,D_132) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_787])).

tff(c_791,plain,(
    ! [A_133,D_134] : k2_xboole_0(k1_tarski(A_133),k1_tarski(D_134)) = k2_tarski(A_133,D_134) ),
    inference(demodulation,[status(thm),theory(equality)],[c_50,c_787])).

tff(c_12,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_10,plain,(
    ! [A_8,B_9] : r1_tarski(k4_xboole_0(A_8,B_9),A_8) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_140,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k3_xboole_0(A_85,B_86)) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_159,plain,(
    ! [A_87] : k5_xboole_0(A_87,A_87) = k4_xboole_0(A_87,A_87) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_140])).

tff(c_64,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_126,plain,(
    ! [A_83,B_84] :
      ( k3_xboole_0(A_83,B_84) = A_83
      | ~ r1_tarski(A_83,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_134,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_64,c_126])).

tff(c_149,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_134,c_140])).

tff(c_165,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_159,c_149])).

tff(c_16,plain,(
    ! [A_13,B_14] : r1_xboole_0(k4_xboole_0(A_13,B_14),B_14) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_323,plain,(
    r1_xboole_0(k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_16])).

tff(c_14,plain,(
    ! [B_12,A_11] :
      ( ~ r1_xboole_0(B_12,A_11)
      | ~ r1_tarski(B_12,A_11)
      | v1_xboole_0(B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_399,plain,
    ( ~ r1_tarski(k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')),k1_tarski('#skF_3'))
    | v1_xboole_0(k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(resolution,[status(thm)],[c_323,c_14])).

tff(c_402,plain,(
    v1_xboole_0(k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_399])).

tff(c_4,plain,(
    ! [A_3] :
      ( k1_xboole_0 = A_3
      | ~ v1_xboole_0(A_3) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_406,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_402,c_4])).

tff(c_18,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k4_xboole_0(B_16,A_15)) = k2_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_419,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_406,c_18])).

tff(c_429,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_12,c_419])).

tff(c_801,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_791,c_429])).

tff(c_548,plain,(
    ! [A_32,B_33,D_109] : k2_xboole_0(k2_tarski(A_32,B_33),k1_tarski(D_109)) = k1_enumset1(A_32,B_33,D_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_545])).

tff(c_819,plain,(
    ! [D_109] : k2_xboole_0(k1_tarski('#skF_4'),k1_tarski(D_109)) = k1_enumset1('#skF_4','#skF_3',D_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_801,c_548])).

tff(c_841,plain,(
    ! [D_141] : k1_enumset1('#skF_4','#skF_3',D_141) = k2_tarski('#skF_4',D_141) ),
    inference(demodulation,[status(thm),theory(equality)],[c_790,c_819])).

tff(c_24,plain,(
    ! [E_23,A_17,C_19] : r2_hidden(E_23,k1_enumset1(A_17,E_23,C_19)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_869,plain,(
    ! [D_141] : r2_hidden('#skF_3',k2_tarski('#skF_4',D_141)) ),
    inference(superposition,[status(thm),theory(equality)],[c_841,c_24])).

tff(c_683,plain,(
    ! [E_119,C_120,B_121,A_122] :
      ( E_119 = C_120
      | E_119 = B_121
      | E_119 = A_122
      | ~ r2_hidden(E_119,k1_enumset1(A_122,B_121,C_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_1255,plain,(
    ! [E_169,B_170,A_171] :
      ( E_169 = B_170
      | E_169 = A_171
      | E_169 = A_171
      | ~ r2_hidden(E_169,k2_tarski(A_171,B_170)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_683])).

tff(c_1258,plain,(
    ! [D_141] :
      ( D_141 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_869,c_1255])).

tff(c_1282,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_62,c_1258])).

tff(c_1276,plain,(
    ! [D_141] : D_141 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_62,c_1258])).

tff(c_1501,plain,(
    ! [D_3361] : D_3361 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_1282,c_1276])).

tff(c_1702,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_1501,c_62])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n017.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 20:31:16 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.39/1.56  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.57  
% 3.39/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.39/1.57  %$ r2_hidden > r1_xboole_0 > r1_tarski > v1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 3.39/1.57  
% 3.39/1.57  %Foreground sorts:
% 3.39/1.57  
% 3.39/1.57  
% 3.39/1.57  %Background operators:
% 3.39/1.57  
% 3.39/1.57  
% 3.39/1.57  %Foreground operators:
% 3.39/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.39/1.57  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.39/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.39/1.57  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.39/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.39/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.39/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.39/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.39/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.39/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.39/1.57  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.39/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.39/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.39/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.39/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.39/1.57  tff('#skF_4', type, '#skF_4': $i).
% 3.39/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.39/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.39/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.39/1.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.39/1.57  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.39/1.57  tff(v1_xboole_0, type, v1_xboole_0: $i > $o).
% 3.39/1.57  
% 3.56/1.58  tff(f_91, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 3.56/1.58  tff(f_76, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.56/1.58  tff(f_74, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.56/1.58  tff(f_78, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.56/1.58  tff(f_72, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 3.56/1.58  tff(f_41, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.56/1.58  tff(f_39, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.56/1.58  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.56/1.58  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.56/1.58  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.56/1.58  tff(f_51, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 3.56/1.58  tff(f_49, axiom, (![A, B]: (~v1_xboole_0(B) => ~(r1_tarski(B, A) & r1_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_xboole_1)).
% 3.56/1.58  tff(f_31, axiom, (![A]: (v1_xboole_0(A) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l13_xboole_0)).
% 3.56/1.58  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.56/1.58  tff(f_68, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.56/1.58  tff(c_62, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.56/1.58  tff(c_50, plain, (![A_32, B_33]: (k1_enumset1(A_32, A_32, B_33)=k2_tarski(A_32, B_33))), inference(cnfTransformation, [status(thm)], [f_76])).
% 3.56/1.58  tff(c_48, plain, (![A_31]: (k2_tarski(A_31, A_31)=k1_tarski(A_31))), inference(cnfTransformation, [status(thm)], [f_74])).
% 3.56/1.58  tff(c_52, plain, (![A_34, B_35, C_36]: (k2_enumset1(A_34, A_34, B_35, C_36)=k1_enumset1(A_34, B_35, C_36))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.56/1.58  tff(c_527, plain, (![A_106, B_107, C_108, D_109]: (k2_xboole_0(k1_enumset1(A_106, B_107, C_108), k1_tarski(D_109))=k2_enumset1(A_106, B_107, C_108, D_109))), inference(cnfTransformation, [status(thm)], [f_72])).
% 3.56/1.58  tff(c_545, plain, (![A_32, B_33, D_109]: (k2_xboole_0(k2_tarski(A_32, B_33), k1_tarski(D_109))=k2_enumset1(A_32, A_32, B_33, D_109))), inference(superposition, [status(thm), theory('equality')], [c_50, c_527])).
% 3.56/1.58  tff(c_778, plain, (![A_130, B_131, D_132]: (k2_xboole_0(k2_tarski(A_130, B_131), k1_tarski(D_132))=k1_enumset1(A_130, B_131, D_132))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_545])).
% 3.56/1.58  tff(c_787, plain, (![A_31, D_132]: (k2_xboole_0(k1_tarski(A_31), k1_tarski(D_132))=k1_enumset1(A_31, A_31, D_132))), inference(superposition, [status(thm), theory('equality')], [c_48, c_778])).
% 3.56/1.58  tff(c_790, plain, (![A_31, D_132]: (k2_xboole_0(k1_tarski(A_31), k1_tarski(D_132))=k2_tarski(A_31, D_132))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_787])).
% 3.56/1.58  tff(c_791, plain, (![A_133, D_134]: (k2_xboole_0(k1_tarski(A_133), k1_tarski(D_134))=k2_tarski(A_133, D_134))), inference(demodulation, [status(thm), theory('equality')], [c_50, c_787])).
% 3.56/1.58  tff(c_12, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.56/1.58  tff(c_10, plain, (![A_8, B_9]: (r1_tarski(k4_xboole_0(A_8, B_9), A_8))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.56/1.58  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.56/1.58  tff(c_140, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k3_xboole_0(A_85, B_86))=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.56/1.58  tff(c_159, plain, (![A_87]: (k5_xboole_0(A_87, A_87)=k4_xboole_0(A_87, A_87))), inference(superposition, [status(thm), theory('equality')], [c_2, c_140])).
% 3.56/1.58  tff(c_64, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_91])).
% 3.56/1.58  tff(c_126, plain, (![A_83, B_84]: (k3_xboole_0(A_83, B_84)=A_83 | ~r1_tarski(A_83, B_84))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.56/1.58  tff(c_134, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_64, c_126])).
% 3.56/1.58  tff(c_149, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_134, c_140])).
% 3.56/1.58  tff(c_165, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_159, c_149])).
% 3.56/1.58  tff(c_16, plain, (![A_13, B_14]: (r1_xboole_0(k4_xboole_0(A_13, B_14), B_14))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.56/1.58  tff(c_323, plain, (r1_xboole_0(k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4')), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_165, c_16])).
% 3.56/1.58  tff(c_14, plain, (![B_12, A_11]: (~r1_xboole_0(B_12, A_11) | ~r1_tarski(B_12, A_11) | v1_xboole_0(B_12))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.56/1.58  tff(c_399, plain, (~r1_tarski(k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4')), k1_tarski('#skF_3')) | v1_xboole_0(k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(resolution, [status(thm)], [c_323, c_14])).
% 3.56/1.58  tff(c_402, plain, (v1_xboole_0(k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_10, c_399])).
% 3.56/1.58  tff(c_4, plain, (![A_3]: (k1_xboole_0=A_3 | ~v1_xboole_0(A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.56/1.58  tff(c_406, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(resolution, [status(thm)], [c_402, c_4])).
% 3.56/1.58  tff(c_18, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k4_xboole_0(B_16, A_15))=k2_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.56/1.58  tff(c_419, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_406, c_18])).
% 3.56/1.58  tff(c_429, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_12, c_419])).
% 3.56/1.58  tff(c_801, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_791, c_429])).
% 3.56/1.58  tff(c_548, plain, (![A_32, B_33, D_109]: (k2_xboole_0(k2_tarski(A_32, B_33), k1_tarski(D_109))=k1_enumset1(A_32, B_33, D_109))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_545])).
% 3.56/1.58  tff(c_819, plain, (![D_109]: (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski(D_109))=k1_enumset1('#skF_4', '#skF_3', D_109))), inference(superposition, [status(thm), theory('equality')], [c_801, c_548])).
% 3.56/1.58  tff(c_841, plain, (![D_141]: (k1_enumset1('#skF_4', '#skF_3', D_141)=k2_tarski('#skF_4', D_141))), inference(demodulation, [status(thm), theory('equality')], [c_790, c_819])).
% 3.56/1.58  tff(c_24, plain, (![E_23, A_17, C_19]: (r2_hidden(E_23, k1_enumset1(A_17, E_23, C_19)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.56/1.58  tff(c_869, plain, (![D_141]: (r2_hidden('#skF_3', k2_tarski('#skF_4', D_141)))), inference(superposition, [status(thm), theory('equality')], [c_841, c_24])).
% 3.56/1.58  tff(c_683, plain, (![E_119, C_120, B_121, A_122]: (E_119=C_120 | E_119=B_121 | E_119=A_122 | ~r2_hidden(E_119, k1_enumset1(A_122, B_121, C_120)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.56/1.58  tff(c_1255, plain, (![E_169, B_170, A_171]: (E_169=B_170 | E_169=A_171 | E_169=A_171 | ~r2_hidden(E_169, k2_tarski(A_171, B_170)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_683])).
% 3.56/1.58  tff(c_1258, plain, (![D_141]: (D_141='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_869, c_1255])).
% 3.56/1.58  tff(c_1282, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_62, c_62, c_1258])).
% 3.56/1.58  tff(c_1276, plain, (![D_141]: (D_141='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_62, c_62, c_1258])).
% 3.56/1.58  tff(c_1501, plain, (![D_3361]: (D_3361='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1282, c_1276])).
% 3.56/1.58  tff(c_1702, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_1501, c_62])).
% 3.56/1.58  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.56/1.58  
% 3.56/1.58  Inference rules
% 3.56/1.58  ----------------------
% 3.56/1.58  #Ref     : 0
% 3.56/1.58  #Sup     : 476
% 3.56/1.58  #Fact    : 0
% 3.56/1.58  #Define  : 0
% 3.56/1.58  #Split   : 0
% 3.56/1.58  #Chain   : 0
% 3.56/1.58  #Close   : 0
% 3.56/1.58  
% 3.56/1.58  Ordering : KBO
% 3.56/1.58  
% 3.56/1.58  Simplification rules
% 3.56/1.58  ----------------------
% 3.56/1.58  #Subsume      : 80
% 3.56/1.58  #Demod        : 209
% 3.56/1.58  #Tautology    : 263
% 3.56/1.58  #SimpNegUnit  : 7
% 3.56/1.58  #BackRed      : 6
% 3.56/1.58  
% 3.56/1.58  #Partial instantiations: 61
% 3.56/1.58  #Strategies tried      : 1
% 3.56/1.58  
% 3.56/1.58  Timing (in seconds)
% 3.56/1.58  ----------------------
% 3.56/1.59  Preprocessing        : 0.34
% 3.56/1.59  Parsing              : 0.18
% 3.56/1.59  CNF conversion       : 0.02
% 3.56/1.59  Main loop            : 0.49
% 3.56/1.59  Inferencing          : 0.20
% 3.56/1.59  Reduction            : 0.17
% 3.56/1.59  Demodulation         : 0.13
% 3.56/1.59  BG Simplification    : 0.03
% 3.56/1.59  Subsumption          : 0.07
% 3.56/1.59  Abstraction          : 0.02
% 3.56/1.59  MUC search           : 0.00
% 3.56/1.59  Cooper               : 0.00
% 3.56/1.59  Total                : 0.86
% 3.56/1.59  Index Insertion      : 0.00
% 3.56/1.59  Index Deletion       : 0.00
% 3.56/1.59  Index Matching       : 0.00
% 3.56/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:16 EST 2020

% Result     : Theorem 3.41s
% Output     : CNFRefutation 3.74s
% Verified   : 
% Statistics : Number of formulae       :   96 ( 194 expanded)
%              Number of leaves         :   35 (  78 expanded)
%              Depth                    :   10
%              Number of atoms          :  115 ( 394 expanded)
%              Number of equality atoms :   76 ( 297 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4

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

tff('#skF_7',type,(
    '#skF_7': $i )).

tff(k5_xboole_0,type,(
    k5_xboole_0: ( $i * $i ) > $i )).

tff(r1_tarski,type,(
    r1_tarski: ( $i * $i ) > $o )).

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i ) > $i )).

tff(f_110,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_48,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_54,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,B)
     => r1_tarski(A,k2_xboole_0(C,B)) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t10_xboole_1)).

tff(f_89,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_64,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t3_boole)).

tff(f_60,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_boole)).

tff(f_50,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_62,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_58,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_66,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_68,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(c_78,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_110,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_78])).

tff(c_76,plain,
    ( k1_xboole_0 != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_109,plain,(
    k1_tarski('#skF_6') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_76])).

tff(c_30,plain,(
    ! [B_13] : r1_tarski(B_13,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_82,plain,(
    k2_xboole_0('#skF_7','#skF_8') = k1_tarski('#skF_6') ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_360,plain,(
    ! [A_86,C_87,B_88] :
      ( r1_tarski(A_86,k2_xboole_0(C_87,B_88))
      | ~ r1_tarski(A_86,B_88) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_372,plain,(
    ! [A_86] :
      ( r1_tarski(A_86,k1_tarski('#skF_6'))
      | ~ r1_tarski(A_86,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_82,c_360])).

tff(c_849,plain,(
    ! [B_122,A_123] :
      ( k1_tarski(B_122) = A_123
      | k1_xboole_0 = A_123
      | ~ r1_tarski(A_123,k1_tarski(B_122)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_871,plain,(
    ! [A_126] :
      ( k1_tarski('#skF_6') = A_126
      | k1_xboole_0 = A_126
      | ~ r1_tarski(A_126,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_372,c_849])).

tff(c_880,plain,
    ( k1_tarski('#skF_6') = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_30,c_871])).

tff(c_883,plain,(
    k1_xboole_0 = '#skF_8' ),
    inference(splitLeft,[status(thm)],[c_880])).

tff(c_42,plain,(
    ! [A_23] : k4_xboole_0(A_23,k1_xboole_0) = A_23 ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_38,plain,(
    ! [A_21] : k3_xboole_0(A_21,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_296,plain,(
    ! [A_70,B_71] : k5_xboole_0(A_70,k3_xboole_0(A_70,B_71)) = k4_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_305,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = k4_xboole_0(A_21,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_296])).

tff(c_308,plain,(
    ! [A_21] : k5_xboole_0(A_21,k1_xboole_0) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_305])).

tff(c_40,plain,(
    ! [A_22] : r1_tarski(k1_xboole_0,A_22) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_183,plain,(
    ! [A_61,B_62] :
      ( k2_xboole_0(A_61,B_62) = B_62
      | ~ r1_tarski(A_61,B_62) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_214,plain,(
    ! [A_66] : k2_xboole_0(k1_xboole_0,A_66) = A_66 ),
    inference(resolution,[status(thm)],[c_40,c_183])).

tff(c_44,plain,(
    ! [A_24,B_25] : k4_xboole_0(A_24,k2_xboole_0(A_24,B_25)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_224,plain,(
    ! [A_66] : k4_xboole_0(k1_xboole_0,A_66) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_44])).

tff(c_440,plain,(
    ! [A_95,B_96] : k5_xboole_0(A_95,k4_xboole_0(B_96,A_95)) = k2_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_449,plain,(
    ! [A_66] : k5_xboole_0(A_66,k1_xboole_0) = k2_xboole_0(A_66,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_224,c_440])).

tff(c_464,plain,(
    ! [A_66] : k2_xboole_0(A_66,k1_xboole_0) = A_66 ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_449])).

tff(c_888,plain,(
    ! [A_66] : k2_xboole_0(A_66,'#skF_8') = A_66 ),
    inference(demodulation,[status(thm),theory(equality)],[c_883,c_464])).

tff(c_1047,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_888,c_82])).

tff(c_1049,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_109,c_1047])).

tff(c_1050,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(splitRight,[status(thm)],[c_880])).

tff(c_1091,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_109])).

tff(c_1092,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_82])).

tff(c_458,plain,(
    ! [A_24,B_25] : k5_xboole_0(k2_xboole_0(A_24,B_25),k1_xboole_0) = k2_xboole_0(k2_xboole_0(A_24,B_25),A_24) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_440])).

tff(c_642,plain,(
    ! [A_107,B_108] : k2_xboole_0(k2_xboole_0(A_107,B_108),A_107) = k2_xboole_0(A_107,B_108) ),
    inference(demodulation,[status(thm),theory(equality)],[c_308,c_458])).

tff(c_34,plain,(
    ! [A_16,C_18,B_17] :
      ( r1_tarski(A_16,k2_xboole_0(C_18,B_17))
      | ~ r1_tarski(A_16,B_17) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_659,plain,(
    ! [A_16,A_107,B_108] :
      ( r1_tarski(A_16,k2_xboole_0(A_107,B_108))
      | ~ r1_tarski(A_16,A_107) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_642,c_34])).

tff(c_1212,plain,(
    ! [A_140] :
      ( r1_tarski(A_140,'#skF_8')
      | ~ r1_tarski(A_140,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1092,c_659])).

tff(c_1221,plain,(
    r1_tarski('#skF_7','#skF_8') ),
    inference(resolution,[status(thm)],[c_30,c_1212])).

tff(c_865,plain,(
    ! [A_86] :
      ( k1_tarski('#skF_6') = A_86
      | k1_xboole_0 = A_86
      | ~ r1_tarski(A_86,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_372,c_849])).

tff(c_1293,plain,(
    ! [A_147] :
      ( A_147 = '#skF_8'
      | k1_xboole_0 = A_147
      | ~ r1_tarski(A_147,'#skF_8') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_865])).

tff(c_1296,plain,
    ( '#skF_7' = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_1221,c_1293])).

tff(c_1308,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_1091,c_1296])).

tff(c_1309,plain,(
    k1_tarski('#skF_6') != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1310,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_78])).

tff(c_1313,plain,(
    ! [A_22] : r1_tarski('#skF_7',A_22) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1310,c_40])).

tff(c_1365,plain,(
    ! [A_156,B_157] :
      ( k2_xboole_0(A_156,B_157) = B_157
      | ~ r1_tarski(A_156,B_157) ) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_1372,plain,(
    ! [A_22] : k2_xboole_0('#skF_7',A_22) = A_22 ),
    inference(resolution,[status(thm)],[c_1313,c_1365])).

tff(c_1386,plain,(
    k1_tarski('#skF_6') = '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1372,c_82])).

tff(c_1388,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1309,c_1386])).

tff(c_1389,plain,(
    k1_xboole_0 != '#skF_8' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_1390,plain,(
    k1_tarski('#skF_6') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_76])).

tff(c_80,plain,
    ( k1_tarski('#skF_6') != '#skF_8'
    | k1_tarski('#skF_6') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_110])).

tff(c_1415,plain,(
    '#skF_7' != '#skF_8' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1390,c_1390,c_80])).

tff(c_1391,plain,(
    k2_xboole_0('#skF_7','#skF_8') = '#skF_7' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1390,c_82])).

tff(c_1697,plain,(
    ! [A_188,C_189,B_190] :
      ( r1_tarski(A_188,k2_xboole_0(C_189,B_190))
      | ~ r1_tarski(A_188,B_190) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_1711,plain,(
    ! [A_188] :
      ( r1_tarski(A_188,'#skF_7')
      | ~ r1_tarski(A_188,'#skF_8') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1391,c_1697])).

tff(c_2034,plain,(
    ! [B_212,A_213] :
      ( k1_tarski(B_212) = A_213
      | k1_xboole_0 = A_213
      | ~ r1_tarski(A_213,k1_tarski(B_212)) ) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_2041,plain,(
    ! [A_213] :
      ( k1_tarski('#skF_6') = A_213
      | k1_xboole_0 = A_213
      | ~ r1_tarski(A_213,'#skF_7') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1390,c_2034])).

tff(c_2058,plain,(
    ! [A_214] :
      ( A_214 = '#skF_7'
      | k1_xboole_0 = A_214
      | ~ r1_tarski(A_214,'#skF_7') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1390,c_2041])).

tff(c_2087,plain,(
    ! [A_215] :
      ( A_215 = '#skF_7'
      | k1_xboole_0 = A_215
      | ~ r1_tarski(A_215,'#skF_8') ) ),
    inference(resolution,[status(thm)],[c_1711,c_2058])).

tff(c_2095,plain,
    ( '#skF_7' = '#skF_8'
    | k1_xboole_0 = '#skF_8' ),
    inference(resolution,[status(thm)],[c_30,c_2087])).

tff(c_2107,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_1389,c_1415,c_2095])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n016.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 14:20:49 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.41/1.62  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.63  
% 3.74/1.63  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.63  %$ r2_hidden > r1_tarski > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_7 > #skF_6 > #skF_2 > #skF_8 > #skF_3 > #skF_1 > #skF_5 > #skF_4
% 3.74/1.63  
% 3.74/1.63  %Foreground sorts:
% 3.74/1.63  
% 3.74/1.63  
% 3.74/1.63  %Background operators:
% 3.74/1.63  
% 3.74/1.63  
% 3.74/1.63  %Foreground operators:
% 3.74/1.63  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.74/1.63  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.74/1.63  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.74/1.63  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.74/1.63  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.74/1.63  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.74/1.63  tff('#skF_7', type, '#skF_7': $i).
% 3.74/1.63  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.74/1.63  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.74/1.63  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.74/1.63  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.74/1.63  tff('#skF_6', type, '#skF_6': $i).
% 3.74/1.63  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.74/1.63  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.74/1.63  tff('#skF_8', type, '#skF_8': $i).
% 3.74/1.63  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.74/1.63  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.74/1.63  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.74/1.63  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.74/1.63  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.74/1.63  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.74/1.63  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.74/1.63  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 3.74/1.63  tff('#skF_4', type, '#skF_4': ($i * $i) > $i).
% 3.74/1.63  
% 3.74/1.65  tff(f_110, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.74/1.65  tff(f_48, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.74/1.65  tff(f_54, axiom, (![A, B, C]: (r1_tarski(A, B) => r1_tarski(A, k2_xboole_0(C, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t10_xboole_1)).
% 3.74/1.65  tff(f_89, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.74/1.65  tff(f_64, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t3_boole)).
% 3.74/1.65  tff(f_60, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_boole)).
% 3.74/1.65  tff(f_50, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.74/1.65  tff(f_62, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.74/1.65  tff(f_58, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.74/1.65  tff(f_66, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_xboole_1)).
% 3.74/1.65  tff(f_68, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.74/1.65  tff(c_78, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.74/1.65  tff(c_110, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_78])).
% 3.74/1.65  tff(c_76, plain, (k1_xboole_0!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.74/1.65  tff(c_109, plain, (k1_tarski('#skF_6')!='#skF_7'), inference(splitLeft, [status(thm)], [c_76])).
% 3.74/1.65  tff(c_30, plain, (![B_13]: (r1_tarski(B_13, B_13))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.74/1.65  tff(c_82, plain, (k2_xboole_0('#skF_7', '#skF_8')=k1_tarski('#skF_6')), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.74/1.65  tff(c_360, plain, (![A_86, C_87, B_88]: (r1_tarski(A_86, k2_xboole_0(C_87, B_88)) | ~r1_tarski(A_86, B_88))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.74/1.65  tff(c_372, plain, (![A_86]: (r1_tarski(A_86, k1_tarski('#skF_6')) | ~r1_tarski(A_86, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_82, c_360])).
% 3.74/1.65  tff(c_849, plain, (![B_122, A_123]: (k1_tarski(B_122)=A_123 | k1_xboole_0=A_123 | ~r1_tarski(A_123, k1_tarski(B_122)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.74/1.65  tff(c_871, plain, (![A_126]: (k1_tarski('#skF_6')=A_126 | k1_xboole_0=A_126 | ~r1_tarski(A_126, '#skF_8'))), inference(resolution, [status(thm)], [c_372, c_849])).
% 3.74/1.65  tff(c_880, plain, (k1_tarski('#skF_6')='#skF_8' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_30, c_871])).
% 3.74/1.65  tff(c_883, plain, (k1_xboole_0='#skF_8'), inference(splitLeft, [status(thm)], [c_880])).
% 3.74/1.65  tff(c_42, plain, (![A_23]: (k4_xboole_0(A_23, k1_xboole_0)=A_23)), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.74/1.65  tff(c_38, plain, (![A_21]: (k3_xboole_0(A_21, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_60])).
% 3.74/1.65  tff(c_296, plain, (![A_70, B_71]: (k5_xboole_0(A_70, k3_xboole_0(A_70, B_71))=k4_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_50])).
% 3.74/1.65  tff(c_305, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=k4_xboole_0(A_21, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_38, c_296])).
% 3.74/1.65  tff(c_308, plain, (![A_21]: (k5_xboole_0(A_21, k1_xboole_0)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_42, c_305])).
% 3.74/1.65  tff(c_40, plain, (![A_22]: (r1_tarski(k1_xboole_0, A_22))), inference(cnfTransformation, [status(thm)], [f_62])).
% 3.74/1.65  tff(c_183, plain, (![A_61, B_62]: (k2_xboole_0(A_61, B_62)=B_62 | ~r1_tarski(A_61, B_62))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.74/1.65  tff(c_214, plain, (![A_66]: (k2_xboole_0(k1_xboole_0, A_66)=A_66)), inference(resolution, [status(thm)], [c_40, c_183])).
% 3.74/1.65  tff(c_44, plain, (![A_24, B_25]: (k4_xboole_0(A_24, k2_xboole_0(A_24, B_25))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.74/1.65  tff(c_224, plain, (![A_66]: (k4_xboole_0(k1_xboole_0, A_66)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_214, c_44])).
% 3.74/1.65  tff(c_440, plain, (![A_95, B_96]: (k5_xboole_0(A_95, k4_xboole_0(B_96, A_95))=k2_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.74/1.65  tff(c_449, plain, (![A_66]: (k5_xboole_0(A_66, k1_xboole_0)=k2_xboole_0(A_66, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_224, c_440])).
% 3.74/1.65  tff(c_464, plain, (![A_66]: (k2_xboole_0(A_66, k1_xboole_0)=A_66)), inference(demodulation, [status(thm), theory('equality')], [c_308, c_449])).
% 3.74/1.65  tff(c_888, plain, (![A_66]: (k2_xboole_0(A_66, '#skF_8')=A_66)), inference(demodulation, [status(thm), theory('equality')], [c_883, c_464])).
% 3.74/1.65  tff(c_1047, plain, (k1_tarski('#skF_6')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_888, c_82])).
% 3.74/1.65  tff(c_1049, plain, $false, inference(negUnitSimplification, [status(thm)], [c_109, c_1047])).
% 3.74/1.65  tff(c_1050, plain, (k1_tarski('#skF_6')='#skF_8'), inference(splitRight, [status(thm)], [c_880])).
% 3.74/1.65  tff(c_1091, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1050, c_109])).
% 3.74/1.65  tff(c_1092, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1050, c_82])).
% 3.74/1.65  tff(c_458, plain, (![A_24, B_25]: (k5_xboole_0(k2_xboole_0(A_24, B_25), k1_xboole_0)=k2_xboole_0(k2_xboole_0(A_24, B_25), A_24))), inference(superposition, [status(thm), theory('equality')], [c_44, c_440])).
% 3.74/1.65  tff(c_642, plain, (![A_107, B_108]: (k2_xboole_0(k2_xboole_0(A_107, B_108), A_107)=k2_xboole_0(A_107, B_108))), inference(demodulation, [status(thm), theory('equality')], [c_308, c_458])).
% 3.74/1.65  tff(c_34, plain, (![A_16, C_18, B_17]: (r1_tarski(A_16, k2_xboole_0(C_18, B_17)) | ~r1_tarski(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.74/1.65  tff(c_659, plain, (![A_16, A_107, B_108]: (r1_tarski(A_16, k2_xboole_0(A_107, B_108)) | ~r1_tarski(A_16, A_107))), inference(superposition, [status(thm), theory('equality')], [c_642, c_34])).
% 3.74/1.65  tff(c_1212, plain, (![A_140]: (r1_tarski(A_140, '#skF_8') | ~r1_tarski(A_140, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1092, c_659])).
% 3.74/1.65  tff(c_1221, plain, (r1_tarski('#skF_7', '#skF_8')), inference(resolution, [status(thm)], [c_30, c_1212])).
% 3.74/1.65  tff(c_865, plain, (![A_86]: (k1_tarski('#skF_6')=A_86 | k1_xboole_0=A_86 | ~r1_tarski(A_86, '#skF_8'))), inference(resolution, [status(thm)], [c_372, c_849])).
% 3.74/1.65  tff(c_1293, plain, (![A_147]: (A_147='#skF_8' | k1_xboole_0=A_147 | ~r1_tarski(A_147, '#skF_8'))), inference(demodulation, [status(thm), theory('equality')], [c_1050, c_865])).
% 3.74/1.65  tff(c_1296, plain, ('#skF_7'='#skF_8' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_1221, c_1293])).
% 3.74/1.65  tff(c_1308, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_1091, c_1296])).
% 3.74/1.65  tff(c_1309, plain, (k1_tarski('#skF_6')!='#skF_8'), inference(splitRight, [status(thm)], [c_78])).
% 3.74/1.65  tff(c_1310, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_78])).
% 3.74/1.65  tff(c_1313, plain, (![A_22]: (r1_tarski('#skF_7', A_22))), inference(demodulation, [status(thm), theory('equality')], [c_1310, c_40])).
% 3.74/1.65  tff(c_1365, plain, (![A_156, B_157]: (k2_xboole_0(A_156, B_157)=B_157 | ~r1_tarski(A_156, B_157))), inference(cnfTransformation, [status(thm)], [f_58])).
% 3.74/1.65  tff(c_1372, plain, (![A_22]: (k2_xboole_0('#skF_7', A_22)=A_22)), inference(resolution, [status(thm)], [c_1313, c_1365])).
% 3.74/1.65  tff(c_1386, plain, (k1_tarski('#skF_6')='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1372, c_82])).
% 3.74/1.65  tff(c_1388, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1309, c_1386])).
% 3.74/1.65  tff(c_1389, plain, (k1_xboole_0!='#skF_8'), inference(splitRight, [status(thm)], [c_76])).
% 3.74/1.65  tff(c_1390, plain, (k1_tarski('#skF_6')='#skF_7'), inference(splitRight, [status(thm)], [c_76])).
% 3.74/1.65  tff(c_80, plain, (k1_tarski('#skF_6')!='#skF_8' | k1_tarski('#skF_6')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_110])).
% 3.74/1.65  tff(c_1415, plain, ('#skF_7'!='#skF_8'), inference(demodulation, [status(thm), theory('equality')], [c_1390, c_1390, c_80])).
% 3.74/1.65  tff(c_1391, plain, (k2_xboole_0('#skF_7', '#skF_8')='#skF_7'), inference(demodulation, [status(thm), theory('equality')], [c_1390, c_82])).
% 3.74/1.65  tff(c_1697, plain, (![A_188, C_189, B_190]: (r1_tarski(A_188, k2_xboole_0(C_189, B_190)) | ~r1_tarski(A_188, B_190))), inference(cnfTransformation, [status(thm)], [f_54])).
% 3.74/1.65  tff(c_1711, plain, (![A_188]: (r1_tarski(A_188, '#skF_7') | ~r1_tarski(A_188, '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1391, c_1697])).
% 3.74/1.65  tff(c_2034, plain, (![B_212, A_213]: (k1_tarski(B_212)=A_213 | k1_xboole_0=A_213 | ~r1_tarski(A_213, k1_tarski(B_212)))), inference(cnfTransformation, [status(thm)], [f_89])).
% 3.74/1.65  tff(c_2041, plain, (![A_213]: (k1_tarski('#skF_6')=A_213 | k1_xboole_0=A_213 | ~r1_tarski(A_213, '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1390, c_2034])).
% 3.74/1.65  tff(c_2058, plain, (![A_214]: (A_214='#skF_7' | k1_xboole_0=A_214 | ~r1_tarski(A_214, '#skF_7'))), inference(demodulation, [status(thm), theory('equality')], [c_1390, c_2041])).
% 3.74/1.65  tff(c_2087, plain, (![A_215]: (A_215='#skF_7' | k1_xboole_0=A_215 | ~r1_tarski(A_215, '#skF_8'))), inference(resolution, [status(thm)], [c_1711, c_2058])).
% 3.74/1.65  tff(c_2095, plain, ('#skF_7'='#skF_8' | k1_xboole_0='#skF_8'), inference(resolution, [status(thm)], [c_30, c_2087])).
% 3.74/1.65  tff(c_2107, plain, $false, inference(negUnitSimplification, [status(thm)], [c_1389, c_1415, c_2095])).
% 3.74/1.65  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.74/1.65  
% 3.74/1.65  Inference rules
% 3.74/1.65  ----------------------
% 3.74/1.65  #Ref     : 0
% 3.74/1.65  #Sup     : 469
% 3.74/1.65  #Fact    : 0
% 3.74/1.65  #Define  : 0
% 3.74/1.65  #Split   : 6
% 3.74/1.65  #Chain   : 0
% 3.74/1.65  #Close   : 0
% 3.74/1.65  
% 3.74/1.65  Ordering : KBO
% 3.74/1.65  
% 3.74/1.65  Simplification rules
% 3.74/1.65  ----------------------
% 3.74/1.65  #Subsume      : 26
% 3.74/1.65  #Demod        : 165
% 3.74/1.65  #Tautology    : 317
% 3.74/1.65  #SimpNegUnit  : 15
% 3.74/1.65  #BackRed      : 43
% 3.74/1.65  
% 3.74/1.65  #Partial instantiations: 0
% 3.74/1.65  #Strategies tried      : 1
% 3.74/1.65  
% 3.74/1.65  Timing (in seconds)
% 3.74/1.65  ----------------------
% 3.74/1.65  Preprocessing        : 0.38
% 3.74/1.65  Parsing              : 0.18
% 3.74/1.65  CNF conversion       : 0.03
% 3.74/1.65  Main loop            : 0.49
% 3.74/1.65  Inferencing          : 0.18
% 3.74/1.65  Reduction            : 0.16
% 3.74/1.65  Demodulation         : 0.11
% 3.74/1.65  BG Simplification    : 0.03
% 3.74/1.65  Subsumption          : 0.09
% 3.74/1.65  Abstraction          : 0.02
% 3.74/1.65  MUC search           : 0.00
% 3.74/1.65  Cooper               : 0.00
% 3.74/1.65  Total                : 0.91
% 3.74/1.65  Index Insertion      : 0.00
% 3.74/1.65  Index Deletion       : 0.00
% 3.74/1.65  Index Matching       : 0.00
% 3.74/1.65  BG Taut test         : 0.00
%------------------------------------------------------------------------------

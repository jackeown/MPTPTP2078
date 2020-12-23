%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n012.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:56 EST 2020

% Result     : Theorem 3.07s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :  102 ( 194 expanded)
%              Number of leaves         :   31 (  73 expanded)
%              Depth                    :    8
%              Number of atoms          :  146 ( 347 expanded)
%              Number of equality atoms :   75 ( 191 expanded)
%              Maximal formula depth    :   12 (   3 average)
%              Maximal term depth       :    2 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_2',type,(
    '#skF_2': $i > $i )).

tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(r2_hidden,type,(
    r2_hidden: ( $i * $i ) > $o )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

tff(k3_enumset1,type,(
    k3_enumset1: ( $i * $i * $i * $i * $i ) > $i )).

tff('#skF_7',type,(
    '#skF_7': $i )).

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

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i ) > $i )).

tff(f_46,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_88,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(A,k1_tarski(B))
      <=> ( A = k1_xboole_0
          | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t39_zfmisc_1)).

tff(f_81,axiom,(
    ! [A,B] :
      ( r1_tarski(k1_tarski(A),B)
    <=> r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l1_zfmisc_1)).

tff(f_40,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_32,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
    <=> ! [C] :
          ( r2_hidden(C,A)
         => r2_hidden(C,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d3_tarski)).

tff(f_65,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_67,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_63,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_48,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(c_14,plain,(
    ! [B_9] : r1_tarski(B_9,B_9) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_64,plain,
    ( ~ r1_tarski('#skF_5',k1_tarski('#skF_6'))
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_87,plain,(
    k1_xboole_0 != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_64])).

tff(c_58,plain,(
    ! [A_46,B_47] :
      ( r1_tarski(k1_tarski(A_46),B_47)
      | ~ r2_hidden(A_46,B_47) ) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_60,plain,
    ( ~ r1_tarski('#skF_5',k1_tarski('#skF_6'))
    | k1_tarski('#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_129,plain,(
    k1_tarski('#skF_8') != '#skF_7' ),
    inference(splitLeft,[status(thm)],[c_60])).

tff(c_70,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_5'
    | r1_tarski('#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_183,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_8')) ),
    inference(splitLeft,[status(thm)],[c_70])).

tff(c_10,plain,(
    ! [B_9,A_8] :
      ( B_9 = A_8
      | ~ r1_tarski(B_9,A_8)
      | ~ r1_tarski(A_8,B_9) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_185,plain,
    ( k1_tarski('#skF_8') = '#skF_7'
    | ~ r1_tarski(k1_tarski('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_183,c_10])).

tff(c_188,plain,(
    ~ r1_tarski(k1_tarski('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_185])).

tff(c_192,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_188])).

tff(c_8,plain,(
    ! [A_6] :
      ( r2_hidden('#skF_2'(A_6),A_6)
      | k1_xboole_0 = A_6 ) ),
    inference(cnfTransformation,[status(thm)],[f_40])).

tff(c_202,plain,(
    ! [C_83,B_84,A_85] :
      ( r2_hidden(C_83,B_84)
      | ~ r2_hidden(C_83,A_85)
      | ~ r1_tarski(A_85,B_84) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_223,plain,(
    ! [A_6,B_84] :
      ( r2_hidden('#skF_2'(A_6),B_84)
      | ~ r1_tarski(A_6,B_84)
      | k1_xboole_0 = A_6 ) ),
    inference(resolution,[status(thm)],[c_8,c_202])).

tff(c_42,plain,(
    ! [A_18] : k2_tarski(A_18,A_18) = k1_tarski(A_18) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_44,plain,(
    ! [A_19,B_20] : k1_enumset1(A_19,A_19,B_20) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_285,plain,(
    ! [E_106,C_107,B_108,A_109] :
      ( E_106 = C_107
      | E_106 = B_108
      | E_106 = A_109
      | ~ r2_hidden(E_106,k1_enumset1(A_109,B_108,C_107)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_353,plain,(
    ! [E_116,B_117,A_118] :
      ( E_116 = B_117
      | E_116 = A_118
      | E_116 = A_118
      | ~ r2_hidden(E_116,k2_tarski(A_118,B_117)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_285])).

tff(c_382,plain,(
    ! [E_119,A_120] :
      ( E_119 = A_120
      | E_119 = A_120
      | E_119 = A_120
      | ~ r2_hidden(E_119,k1_tarski(A_120)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_353])).

tff(c_429,plain,(
    ! [A_127,A_128] :
      ( A_127 = '#skF_2'(A_128)
      | ~ r1_tarski(A_128,k1_tarski(A_127))
      | k1_xboole_0 = A_128 ) ),
    inference(resolution,[status(thm)],[c_223,c_382])).

tff(c_432,plain,
    ( '#skF_2'('#skF_7') = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_183,c_429])).

tff(c_447,plain,(
    '#skF_2'('#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_432])).

tff(c_458,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_8])).

tff(c_463,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_192,c_458])).

tff(c_464,plain,
    ( k1_xboole_0 = '#skF_5'
    | k1_tarski('#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_70])).

tff(c_466,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_464])).

tff(c_68,plain,
    ( ~ r1_tarski('#skF_5',k1_tarski('#skF_6'))
    | r1_tarski('#skF_7',k1_tarski('#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_130,plain,(
    ~ r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(splitLeft,[status(thm)],[c_68])).

tff(c_467,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_466,c_130])).

tff(c_470,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_467])).

tff(c_471,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_464])).

tff(c_16,plain,(
    ! [A_10] : r1_tarski(k1_xboole_0,A_10) ),
    inference(cnfTransformation,[status(thm)],[f_48])).

tff(c_477,plain,(
    ! [A_10] : r1_tarski('#skF_5',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_471,c_16])).

tff(c_484,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_477,c_130])).

tff(c_485,plain,(
    r1_tarski('#skF_7',k1_tarski('#skF_8')) ),
    inference(splitRight,[status(thm)],[c_68])).

tff(c_488,plain,(
    ! [B_131,A_132] :
      ( B_131 = A_132
      | ~ r1_tarski(B_131,A_132)
      | ~ r1_tarski(A_132,B_131) ) ),
    inference(cnfTransformation,[status(thm)],[f_46])).

tff(c_492,plain,
    ( k1_tarski('#skF_8') = '#skF_7'
    | ~ r1_tarski(k1_tarski('#skF_8'),'#skF_7') ),
    inference(resolution,[status(thm)],[c_485,c_488])).

tff(c_502,plain,(
    ~ r1_tarski(k1_tarski('#skF_8'),'#skF_7') ),
    inference(negUnitSimplification,[status(thm)],[c_129,c_492])).

tff(c_512,plain,(
    ~ r2_hidden('#skF_8','#skF_7') ),
    inference(resolution,[status(thm)],[c_58,c_502])).

tff(c_556,plain,(
    ! [C_137,B_138,A_139] :
      ( r2_hidden(C_137,B_138)
      | ~ r2_hidden(C_137,A_139)
      | ~ r1_tarski(A_139,B_138) ) ),
    inference(cnfTransformation,[status(thm)],[f_32])).

tff(c_577,plain,(
    ! [A_6,B_138] :
      ( r2_hidden('#skF_2'(A_6),B_138)
      | ~ r1_tarski(A_6,B_138)
      | k1_xboole_0 = A_6 ) ),
    inference(resolution,[status(thm)],[c_8,c_556])).

tff(c_687,plain,(
    ! [E_169,C_170,B_171,A_172] :
      ( E_169 = C_170
      | E_169 = B_171
      | E_169 = A_172
      | ~ r2_hidden(E_169,k1_enumset1(A_172,B_171,C_170)) ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_740,plain,(
    ! [E_176,B_177,A_178] :
      ( E_176 = B_177
      | E_176 = A_178
      | E_176 = A_178
      | ~ r2_hidden(E_176,k2_tarski(A_178,B_177)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_687])).

tff(c_774,plain,(
    ! [E_179,A_180] :
      ( E_179 = A_180
      | E_179 = A_180
      | E_179 = A_180
      | ~ r2_hidden(E_179,k1_tarski(A_180)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_740])).

tff(c_817,plain,(
    ! [A_182,A_183] :
      ( A_182 = '#skF_2'(A_183)
      | ~ r1_tarski(A_183,k1_tarski(A_182))
      | k1_xboole_0 = A_183 ) ),
    inference(resolution,[status(thm)],[c_577,c_774])).

tff(c_823,plain,
    ( '#skF_2'('#skF_7') = '#skF_8'
    | k1_xboole_0 = '#skF_7' ),
    inference(resolution,[status(thm)],[c_485,c_817])).

tff(c_839,plain,(
    '#skF_2'('#skF_7') = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_823])).

tff(c_859,plain,
    ( r2_hidden('#skF_8','#skF_7')
    | k1_xboole_0 = '#skF_7' ),
    inference(superposition,[status(thm),theory(equality)],[c_839,c_8])).

tff(c_864,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_87,c_512,c_859])).

tff(c_866,plain,(
    k1_tarski('#skF_8') = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_62,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_5'
    | k1_tarski('#skF_8') != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_987,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_866,c_62])).

tff(c_988,plain,(
    k1_xboole_0 = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_987])).

tff(c_994,plain,(
    ! [A_10] : r1_tarski('#skF_5',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_988,c_16])).

tff(c_865,plain,(
    ~ r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_60])).

tff(c_1001,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_994,c_865])).

tff(c_1002,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_987])).

tff(c_1004,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1002,c_865])).

tff(c_1007,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1004])).

tff(c_1009,plain,(
    k1_xboole_0 = '#skF_7' ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_66,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | k1_xboole_0 = '#skF_5'
    | k1_xboole_0 != '#skF_7' ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_1060,plain,
    ( k1_tarski('#skF_6') = '#skF_5'
    | '#skF_7' = '#skF_5' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1009,c_1009,c_66])).

tff(c_1061,plain,(
    '#skF_7' = '#skF_5' ),
    inference(splitLeft,[status(thm)],[c_1060])).

tff(c_1011,plain,(
    ! [A_10] : r1_tarski('#skF_7',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1009,c_16])).

tff(c_1063,plain,(
    ! [A_10] : r1_tarski('#skF_5',A_10) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1061,c_1011])).

tff(c_1008,plain,(
    ~ r1_tarski('#skF_5',k1_tarski('#skF_6')) ),
    inference(splitRight,[status(thm)],[c_64])).

tff(c_1076,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1063,c_1008])).

tff(c_1077,plain,(
    k1_tarski('#skF_6') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_1060])).

tff(c_1079,plain,(
    ~ r1_tarski('#skF_5','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1077,c_1008])).

tff(c_1082,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1079])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n012.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 09:53:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.07/1.52  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.07/1.52  
% 3.07/1.52  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.53  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_8 > #skF_3 > #skF_1
% 3.15/1.53  
% 3.15/1.53  %Foreground sorts:
% 3.15/1.53  
% 3.15/1.53  
% 3.15/1.53  %Background operators:
% 3.15/1.53  
% 3.15/1.53  
% 3.15/1.53  %Foreground operators:
% 3.15/1.53  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.15/1.53  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.53  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.15/1.53  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.15/1.53  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.53  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.15/1.53  tff('#skF_7', type, '#skF_7': $i).
% 3.15/1.53  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.53  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.15/1.53  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.53  tff('#skF_5', type, '#skF_5': $i).
% 3.15/1.53  tff('#skF_6', type, '#skF_6': $i).
% 3.15/1.53  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.15/1.53  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.53  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.15/1.53  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.53  tff('#skF_8', type, '#skF_8': $i).
% 3.15/1.53  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.53  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.53  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.15/1.53  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.53  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.15/1.53  
% 3.15/1.54  tff(f_46, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 3.15/1.54  tff(f_88, negated_conjecture, ~(![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t39_zfmisc_1)).
% 3.15/1.54  tff(f_81, axiom, (![A, B]: (r1_tarski(k1_tarski(A), B) <=> r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l1_zfmisc_1)).
% 3.15/1.54  tff(f_40, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.15/1.54  tff(f_32, axiom, (![A, B]: (r1_tarski(A, B) <=> (![C]: (r2_hidden(C, A) => r2_hidden(C, B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d3_tarski)).
% 3.15/1.54  tff(f_65, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.15/1.54  tff(f_67, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 3.15/1.54  tff(f_63, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.15/1.54  tff(f_48, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.15/1.54  tff(c_14, plain, (![B_9]: (r1_tarski(B_9, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.15/1.54  tff(c_64, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_6')) | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.15/1.54  tff(c_87, plain, (k1_xboole_0!='#skF_7'), inference(splitLeft, [status(thm)], [c_64])).
% 3.15/1.54  tff(c_58, plain, (![A_46, B_47]: (r1_tarski(k1_tarski(A_46), B_47) | ~r2_hidden(A_46, B_47))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.15/1.54  tff(c_60, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_6')) | k1_tarski('#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.15/1.54  tff(c_129, plain, (k1_tarski('#skF_8')!='#skF_7'), inference(splitLeft, [status(thm)], [c_60])).
% 3.15/1.54  tff(c_70, plain, (k1_tarski('#skF_6')='#skF_5' | k1_xboole_0='#skF_5' | r1_tarski('#skF_7', k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.15/1.54  tff(c_183, plain, (r1_tarski('#skF_7', k1_tarski('#skF_8'))), inference(splitLeft, [status(thm)], [c_70])).
% 3.15/1.54  tff(c_10, plain, (![B_9, A_8]: (B_9=A_8 | ~r1_tarski(B_9, A_8) | ~r1_tarski(A_8, B_9))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.15/1.54  tff(c_185, plain, (k1_tarski('#skF_8')='#skF_7' | ~r1_tarski(k1_tarski('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_183, c_10])).
% 3.15/1.54  tff(c_188, plain, (~r1_tarski(k1_tarski('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_129, c_185])).
% 3.15/1.54  tff(c_192, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_58, c_188])).
% 3.15/1.54  tff(c_8, plain, (![A_6]: (r2_hidden('#skF_2'(A_6), A_6) | k1_xboole_0=A_6)), inference(cnfTransformation, [status(thm)], [f_40])).
% 3.15/1.54  tff(c_202, plain, (![C_83, B_84, A_85]: (r2_hidden(C_83, B_84) | ~r2_hidden(C_83, A_85) | ~r1_tarski(A_85, B_84))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.15/1.54  tff(c_223, plain, (![A_6, B_84]: (r2_hidden('#skF_2'(A_6), B_84) | ~r1_tarski(A_6, B_84) | k1_xboole_0=A_6)), inference(resolution, [status(thm)], [c_8, c_202])).
% 3.15/1.54  tff(c_42, plain, (![A_18]: (k2_tarski(A_18, A_18)=k1_tarski(A_18))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.54  tff(c_44, plain, (![A_19, B_20]: (k1_enumset1(A_19, A_19, B_20)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.15/1.54  tff(c_285, plain, (![E_106, C_107, B_108, A_109]: (E_106=C_107 | E_106=B_108 | E_106=A_109 | ~r2_hidden(E_106, k1_enumset1(A_109, B_108, C_107)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.15/1.54  tff(c_353, plain, (![E_116, B_117, A_118]: (E_116=B_117 | E_116=A_118 | E_116=A_118 | ~r2_hidden(E_116, k2_tarski(A_118, B_117)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_285])).
% 3.15/1.54  tff(c_382, plain, (![E_119, A_120]: (E_119=A_120 | E_119=A_120 | E_119=A_120 | ~r2_hidden(E_119, k1_tarski(A_120)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_353])).
% 3.15/1.54  tff(c_429, plain, (![A_127, A_128]: (A_127='#skF_2'(A_128) | ~r1_tarski(A_128, k1_tarski(A_127)) | k1_xboole_0=A_128)), inference(resolution, [status(thm)], [c_223, c_382])).
% 3.15/1.54  tff(c_432, plain, ('#skF_2'('#skF_7')='#skF_8' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_183, c_429])).
% 3.15/1.54  tff(c_447, plain, ('#skF_2'('#skF_7')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_87, c_432])).
% 3.15/1.54  tff(c_458, plain, (r2_hidden('#skF_8', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_447, c_8])).
% 3.15/1.54  tff(c_463, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_192, c_458])).
% 3.15/1.54  tff(c_464, plain, (k1_xboole_0='#skF_5' | k1_tarski('#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_70])).
% 3.15/1.54  tff(c_466, plain, (k1_tarski('#skF_6')='#skF_5'), inference(splitLeft, [status(thm)], [c_464])).
% 3.15/1.54  tff(c_68, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_6')) | r1_tarski('#skF_7', k1_tarski('#skF_8'))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.15/1.54  tff(c_130, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(splitLeft, [status(thm)], [c_68])).
% 3.15/1.54  tff(c_467, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_466, c_130])).
% 3.15/1.54  tff(c_470, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_467])).
% 3.15/1.54  tff(c_471, plain, (k1_xboole_0='#skF_5'), inference(splitRight, [status(thm)], [c_464])).
% 3.15/1.54  tff(c_16, plain, (![A_10]: (r1_tarski(k1_xboole_0, A_10))), inference(cnfTransformation, [status(thm)], [f_48])).
% 3.15/1.54  tff(c_477, plain, (![A_10]: (r1_tarski('#skF_5', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_471, c_16])).
% 3.15/1.54  tff(c_484, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_477, c_130])).
% 3.15/1.54  tff(c_485, plain, (r1_tarski('#skF_7', k1_tarski('#skF_8'))), inference(splitRight, [status(thm)], [c_68])).
% 3.15/1.54  tff(c_488, plain, (![B_131, A_132]: (B_131=A_132 | ~r1_tarski(B_131, A_132) | ~r1_tarski(A_132, B_131))), inference(cnfTransformation, [status(thm)], [f_46])).
% 3.15/1.54  tff(c_492, plain, (k1_tarski('#skF_8')='#skF_7' | ~r1_tarski(k1_tarski('#skF_8'), '#skF_7')), inference(resolution, [status(thm)], [c_485, c_488])).
% 3.15/1.54  tff(c_502, plain, (~r1_tarski(k1_tarski('#skF_8'), '#skF_7')), inference(negUnitSimplification, [status(thm)], [c_129, c_492])).
% 3.15/1.54  tff(c_512, plain, (~r2_hidden('#skF_8', '#skF_7')), inference(resolution, [status(thm)], [c_58, c_502])).
% 3.15/1.54  tff(c_556, plain, (![C_137, B_138, A_139]: (r2_hidden(C_137, B_138) | ~r2_hidden(C_137, A_139) | ~r1_tarski(A_139, B_138))), inference(cnfTransformation, [status(thm)], [f_32])).
% 3.15/1.54  tff(c_577, plain, (![A_6, B_138]: (r2_hidden('#skF_2'(A_6), B_138) | ~r1_tarski(A_6, B_138) | k1_xboole_0=A_6)), inference(resolution, [status(thm)], [c_8, c_556])).
% 3.15/1.54  tff(c_687, plain, (![E_169, C_170, B_171, A_172]: (E_169=C_170 | E_169=B_171 | E_169=A_172 | ~r2_hidden(E_169, k1_enumset1(A_172, B_171, C_170)))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.15/1.54  tff(c_740, plain, (![E_176, B_177, A_178]: (E_176=B_177 | E_176=A_178 | E_176=A_178 | ~r2_hidden(E_176, k2_tarski(A_178, B_177)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_687])).
% 3.15/1.54  tff(c_774, plain, (![E_179, A_180]: (E_179=A_180 | E_179=A_180 | E_179=A_180 | ~r2_hidden(E_179, k1_tarski(A_180)))), inference(superposition, [status(thm), theory('equality')], [c_42, c_740])).
% 3.15/1.54  tff(c_817, plain, (![A_182, A_183]: (A_182='#skF_2'(A_183) | ~r1_tarski(A_183, k1_tarski(A_182)) | k1_xboole_0=A_183)), inference(resolution, [status(thm)], [c_577, c_774])).
% 3.15/1.54  tff(c_823, plain, ('#skF_2'('#skF_7')='#skF_8' | k1_xboole_0='#skF_7'), inference(resolution, [status(thm)], [c_485, c_817])).
% 3.15/1.54  tff(c_839, plain, ('#skF_2'('#skF_7')='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_87, c_823])).
% 3.15/1.54  tff(c_859, plain, (r2_hidden('#skF_8', '#skF_7') | k1_xboole_0='#skF_7'), inference(superposition, [status(thm), theory('equality')], [c_839, c_8])).
% 3.15/1.54  tff(c_864, plain, $false, inference(negUnitSimplification, [status(thm)], [c_87, c_512, c_859])).
% 3.15/1.54  tff(c_866, plain, (k1_tarski('#skF_8')='#skF_7'), inference(splitRight, [status(thm)], [c_60])).
% 3.15/1.54  tff(c_62, plain, (k1_tarski('#skF_6')='#skF_5' | k1_xboole_0='#skF_5' | k1_tarski('#skF_8')!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.15/1.54  tff(c_987, plain, (k1_tarski('#skF_6')='#skF_5' | k1_xboole_0='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_866, c_62])).
% 3.15/1.54  tff(c_988, plain, (k1_xboole_0='#skF_5'), inference(splitLeft, [status(thm)], [c_987])).
% 3.15/1.54  tff(c_994, plain, (![A_10]: (r1_tarski('#skF_5', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_988, c_16])).
% 3.15/1.54  tff(c_865, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_60])).
% 3.15/1.54  tff(c_1001, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_994, c_865])).
% 3.15/1.54  tff(c_1002, plain, (k1_tarski('#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_987])).
% 3.15/1.54  tff(c_1004, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1002, c_865])).
% 3.15/1.54  tff(c_1007, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_1004])).
% 3.15/1.54  tff(c_1009, plain, (k1_xboole_0='#skF_7'), inference(splitRight, [status(thm)], [c_64])).
% 3.15/1.54  tff(c_66, plain, (k1_tarski('#skF_6')='#skF_5' | k1_xboole_0='#skF_5' | k1_xboole_0!='#skF_7'), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.15/1.54  tff(c_1060, plain, (k1_tarski('#skF_6')='#skF_5' | '#skF_7'='#skF_5'), inference(demodulation, [status(thm), theory('equality')], [c_1009, c_1009, c_66])).
% 3.15/1.54  tff(c_1061, plain, ('#skF_7'='#skF_5'), inference(splitLeft, [status(thm)], [c_1060])).
% 3.15/1.54  tff(c_1011, plain, (![A_10]: (r1_tarski('#skF_7', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_1009, c_16])).
% 3.15/1.54  tff(c_1063, plain, (![A_10]: (r1_tarski('#skF_5', A_10))), inference(demodulation, [status(thm), theory('equality')], [c_1061, c_1011])).
% 3.15/1.54  tff(c_1008, plain, (~r1_tarski('#skF_5', k1_tarski('#skF_6'))), inference(splitRight, [status(thm)], [c_64])).
% 3.15/1.54  tff(c_1076, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1063, c_1008])).
% 3.15/1.54  tff(c_1077, plain, (k1_tarski('#skF_6')='#skF_5'), inference(splitRight, [status(thm)], [c_1060])).
% 3.15/1.54  tff(c_1079, plain, (~r1_tarski('#skF_5', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_1077, c_1008])).
% 3.15/1.54  tff(c_1082, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_14, c_1079])).
% 3.15/1.54  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.15/1.54  
% 3.15/1.54  Inference rules
% 3.15/1.54  ----------------------
% 3.15/1.54  #Ref     : 0
% 3.15/1.54  #Sup     : 205
% 3.15/1.54  #Fact    : 0
% 3.15/1.54  #Define  : 0
% 3.15/1.54  #Split   : 8
% 3.15/1.54  #Chain   : 0
% 3.15/1.54  #Close   : 0
% 3.15/1.54  
% 3.15/1.54  Ordering : KBO
% 3.15/1.54  
% 3.15/1.54  Simplification rules
% 3.15/1.54  ----------------------
% 3.15/1.54  #Subsume      : 28
% 3.15/1.55  #Demod        : 72
% 3.15/1.55  #Tautology    : 97
% 3.15/1.55  #SimpNegUnit  : 11
% 3.15/1.55  #BackRed      : 22
% 3.15/1.55  
% 3.15/1.55  #Partial instantiations: 0
% 3.15/1.55  #Strategies tried      : 1
% 3.15/1.55  
% 3.15/1.55  Timing (in seconds)
% 3.15/1.55  ----------------------
% 3.15/1.55  Preprocessing        : 0.36
% 3.15/1.55  Parsing              : 0.18
% 3.15/1.55  CNF conversion       : 0.03
% 3.15/1.55  Main loop            : 0.37
% 3.15/1.55  Inferencing          : 0.14
% 3.15/1.55  Reduction            : 0.11
% 3.15/1.55  Demodulation         : 0.08
% 3.15/1.55  BG Simplification    : 0.03
% 3.15/1.55  Subsumption          : 0.07
% 3.15/1.55  Abstraction          : 0.02
% 3.15/1.55  MUC search           : 0.00
% 3.15/1.55  Cooper               : 0.00
% 3.15/1.55  Total                : 0.77
% 3.15/1.55  Index Insertion      : 0.00
% 3.15/1.55  Index Deletion       : 0.00
% 3.15/1.55  Index Matching       : 0.00
% 3.15/1.55  BG Taut test         : 0.00
%------------------------------------------------------------------------------

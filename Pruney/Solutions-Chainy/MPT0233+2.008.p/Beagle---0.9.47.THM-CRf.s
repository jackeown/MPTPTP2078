%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n020.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:25 EST 2020

% Result     : Theorem 3.34s
% Output     : CNFRefutation 3.34s
% Verified   : 
% Statistics : Number of formulae       :   87 ( 107 expanded)
%              Number of leaves         :   42 (  53 expanded)
%              Depth                    :   16
%              Number of atoms          :   82 ( 111 expanded)
%              Number of equality atoms :   58 (  78 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_103,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_79,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_93,axiom,(
    ! [A,B] : r1_tarski(k1_tarski(A),k2_tarski(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d2_tarski)).

tff(c_86,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_84,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_72,plain,(
    ! [A_44,B_45,C_46] : k2_enumset1(A_44,A_44,B_45,C_46) = k1_enumset1(A_44,B_45,C_46) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_68,plain,(
    ! [A_41] : k2_tarski(A_41,A_41) = k1_tarski(A_41) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_1291,plain,(
    ! [A_164,B_165,C_166,D_167] : k2_xboole_0(k2_tarski(A_164,B_165),k2_tarski(C_166,D_167)) = k2_enumset1(A_164,B_165,C_166,D_167) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1332,plain,(
    ! [A_41,C_166,D_167] : k2_xboole_0(k1_tarski(A_41),k2_tarski(C_166,D_167)) = k2_enumset1(A_41,A_41,C_166,D_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_68,c_1291])).

tff(c_1457,plain,(
    ! [A_176,C_177,D_178] : k2_xboole_0(k1_tarski(A_176),k2_tarski(C_177,D_178)) = k1_enumset1(A_176,C_177,D_178) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1332])).

tff(c_18,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_14] : r1_tarski(k1_xboole_0,A_14) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_222,plain,(
    ! [A_94,B_95] :
      ( k3_xboole_0(A_94,B_95) = A_94
      | ~ r1_tarski(A_94,B_95) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_244,plain,(
    ! [A_96] : k3_xboole_0(k1_xboole_0,A_96) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_14,c_222])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_249,plain,(
    ! [A_96] : k3_xboole_0(A_96,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_244,c_4])).

tff(c_438,plain,(
    ! [A_108,B_109] : k5_xboole_0(A_108,k3_xboole_0(A_108,B_109)) = k4_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_447,plain,(
    ! [A_96] : k5_xboole_0(A_96,k1_xboole_0) = k4_xboole_0(A_96,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_249,c_438])).

tff(c_488,plain,(
    ! [A_111] : k4_xboole_0(A_111,k1_xboole_0) = A_111 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_447])).

tff(c_16,plain,(
    ! [A_15,B_16] : k4_xboole_0(A_15,k4_xboole_0(A_15,B_16)) = k3_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_498,plain,(
    ! [A_111] : k4_xboole_0(A_111,A_111) = k3_xboole_0(A_111,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_16])).

tff(c_508,plain,(
    ! [A_111] : k4_xboole_0(A_111,A_111) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_249,c_498])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_462,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_438])).

tff(c_540,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_462])).

tff(c_82,plain,(
    ! [A_65,B_66] : r1_tarski(k1_tarski(A_65),k2_tarski(A_65,B_66)) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_88,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_238,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_88,c_222])).

tff(c_336,plain,(
    ! [A_100,B_101,C_102] :
      ( r1_tarski(A_100,B_101)
      | ~ r1_tarski(A_100,k3_xboole_0(B_101,C_102)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_825,plain,(
    ! [A_127,B_128,A_129] :
      ( r1_tarski(A_127,B_128)
      | ~ r1_tarski(A_127,k3_xboole_0(A_129,B_128)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_336])).

tff(c_990,plain,(
    ! [A_144] :
      ( r1_tarski(A_144,k2_tarski('#skF_7','#skF_8'))
      | ~ r1_tarski(A_144,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_238,c_825])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1185,plain,(
    ! [A_162] :
      ( k3_xboole_0(A_162,k2_tarski('#skF_7','#skF_8')) = A_162
      | ~ r1_tarski(A_162,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_990,c_12])).

tff(c_1199,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_82,c_1185])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1217,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1199,c_8])).

tff(c_1224,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_540,c_1217])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1229,plain,(
    k2_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_5')) = k5_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1224,c_20])).

tff(c_1235,plain,(
    k2_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_5')) = k2_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1229])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1272,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1235,c_2])).

tff(c_1463,plain,(
    k1_enumset1('#skF_5','#skF_7','#skF_8') = k2_tarski('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1457,c_1272])).

tff(c_28,plain,(
    ! [E_26,B_21,C_22] : r2_hidden(E_26,k1_enumset1(E_26,B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1511,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1463,c_28])).

tff(c_46,plain,(
    ! [D_32,B_28,A_27] :
      ( D_32 = B_28
      | D_32 = A_27
      | ~ r2_hidden(D_32,k2_tarski(A_27,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1544,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1511,c_46])).

tff(c_1548,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_86,c_84,c_1544])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n020.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:41:52 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.34/1.61  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.62  
% 3.34/1.62  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.62  %$ r2_hidden > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 3.34/1.62  
% 3.34/1.62  %Foreground sorts:
% 3.34/1.62  
% 3.34/1.62  
% 3.34/1.62  %Background operators:
% 3.34/1.62  
% 3.34/1.62  
% 3.34/1.62  %Foreground operators:
% 3.34/1.62  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.34/1.62  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.34/1.62  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.34/1.62  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.34/1.62  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.34/1.62  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.34/1.62  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.34/1.62  tff('#skF_7', type, '#skF_7': $i).
% 3.34/1.62  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.34/1.62  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.34/1.62  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.34/1.62  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.34/1.62  tff('#skF_5', type, '#skF_5': $i).
% 3.34/1.62  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.34/1.62  tff('#skF_6', type, '#skF_6': $i).
% 3.34/1.62  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.34/1.62  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.62  tff('#skF_8', type, '#skF_8': $i).
% 3.34/1.62  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.34/1.62  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.34/1.62  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.34/1.62  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.34/1.62  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.34/1.62  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.34/1.62  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.34/1.62  
% 3.34/1.64  tff(f_103, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.34/1.64  tff(f_83, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 3.34/1.64  tff(f_79, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 3.34/1.64  tff(f_75, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l53_enumset1)).
% 3.34/1.64  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.34/1.64  tff(f_43, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.34/1.64  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.34/1.64  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.34/1.64  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.34/1.64  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.34/1.64  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.34/1.64  tff(f_93, axiom, (![A, B]: r1_tarski(k1_tarski(A), k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_zfmisc_1)).
% 3.34/1.64  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.34/1.64  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.34/1.64  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 3.34/1.64  tff(f_64, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 3.34/1.64  tff(f_73, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d2_tarski)).
% 3.34/1.64  tff(c_86, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.34/1.64  tff(c_84, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.34/1.64  tff(c_72, plain, (![A_44, B_45, C_46]: (k2_enumset1(A_44, A_44, B_45, C_46)=k1_enumset1(A_44, B_45, C_46))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.34/1.64  tff(c_68, plain, (![A_41]: (k2_tarski(A_41, A_41)=k1_tarski(A_41))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.34/1.64  tff(c_1291, plain, (![A_164, B_165, C_166, D_167]: (k2_xboole_0(k2_tarski(A_164, B_165), k2_tarski(C_166, D_167))=k2_enumset1(A_164, B_165, C_166, D_167))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.34/1.64  tff(c_1332, plain, (![A_41, C_166, D_167]: (k2_xboole_0(k1_tarski(A_41), k2_tarski(C_166, D_167))=k2_enumset1(A_41, A_41, C_166, D_167))), inference(superposition, [status(thm), theory('equality')], [c_68, c_1291])).
% 3.34/1.64  tff(c_1457, plain, (![A_176, C_177, D_178]: (k2_xboole_0(k1_tarski(A_176), k2_tarski(C_177, D_178))=k1_enumset1(A_176, C_177, D_178))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1332])).
% 3.34/1.64  tff(c_18, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.34/1.64  tff(c_14, plain, (![A_14]: (r1_tarski(k1_xboole_0, A_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.34/1.64  tff(c_222, plain, (![A_94, B_95]: (k3_xboole_0(A_94, B_95)=A_94 | ~r1_tarski(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.34/1.64  tff(c_244, plain, (![A_96]: (k3_xboole_0(k1_xboole_0, A_96)=k1_xboole_0)), inference(resolution, [status(thm)], [c_14, c_222])).
% 3.34/1.64  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.34/1.64  tff(c_249, plain, (![A_96]: (k3_xboole_0(A_96, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_244, c_4])).
% 3.34/1.64  tff(c_438, plain, (![A_108, B_109]: (k5_xboole_0(A_108, k3_xboole_0(A_108, B_109))=k4_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.34/1.64  tff(c_447, plain, (![A_96]: (k5_xboole_0(A_96, k1_xboole_0)=k4_xboole_0(A_96, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_249, c_438])).
% 3.34/1.64  tff(c_488, plain, (![A_111]: (k4_xboole_0(A_111, k1_xboole_0)=A_111)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_447])).
% 3.34/1.64  tff(c_16, plain, (![A_15, B_16]: (k4_xboole_0(A_15, k4_xboole_0(A_15, B_16))=k3_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.34/1.64  tff(c_498, plain, (![A_111]: (k4_xboole_0(A_111, A_111)=k3_xboole_0(A_111, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_488, c_16])).
% 3.34/1.64  tff(c_508, plain, (![A_111]: (k4_xboole_0(A_111, A_111)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_249, c_498])).
% 3.34/1.64  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.34/1.64  tff(c_462, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_438])).
% 3.34/1.64  tff(c_540, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_508, c_462])).
% 3.34/1.64  tff(c_82, plain, (![A_65, B_66]: (r1_tarski(k1_tarski(A_65), k2_tarski(A_65, B_66)))), inference(cnfTransformation, [status(thm)], [f_93])).
% 3.34/1.64  tff(c_88, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 3.34/1.64  tff(c_238, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_88, c_222])).
% 3.34/1.64  tff(c_336, plain, (![A_100, B_101, C_102]: (r1_tarski(A_100, B_101) | ~r1_tarski(A_100, k3_xboole_0(B_101, C_102)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.34/1.64  tff(c_825, plain, (![A_127, B_128, A_129]: (r1_tarski(A_127, B_128) | ~r1_tarski(A_127, k3_xboole_0(A_129, B_128)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_336])).
% 3.34/1.64  tff(c_990, plain, (![A_144]: (r1_tarski(A_144, k2_tarski('#skF_7', '#skF_8')) | ~r1_tarski(A_144, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_238, c_825])).
% 3.34/1.64  tff(c_12, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.34/1.64  tff(c_1185, plain, (![A_162]: (k3_xboole_0(A_162, k2_tarski('#skF_7', '#skF_8'))=A_162 | ~r1_tarski(A_162, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_990, c_12])).
% 3.34/1.64  tff(c_1199, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_82, c_1185])).
% 3.34/1.64  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.34/1.64  tff(c_1217, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1199, c_8])).
% 3.34/1.64  tff(c_1224, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_540, c_1217])).
% 3.34/1.64  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.34/1.64  tff(c_1229, plain, (k2_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_5'))=k5_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1224, c_20])).
% 3.34/1.64  tff(c_1235, plain, (k2_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_5'))=k2_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1229])).
% 3.34/1.64  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.34/1.64  tff(c_1272, plain, (k2_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1235, c_2])).
% 3.34/1.64  tff(c_1463, plain, (k1_enumset1('#skF_5', '#skF_7', '#skF_8')=k2_tarski('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1457, c_1272])).
% 3.34/1.64  tff(c_28, plain, (![E_26, B_21, C_22]: (r2_hidden(E_26, k1_enumset1(E_26, B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.34/1.64  tff(c_1511, plain, (r2_hidden('#skF_5', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1463, c_28])).
% 3.34/1.64  tff(c_46, plain, (![D_32, B_28, A_27]: (D_32=B_28 | D_32=A_27 | ~r2_hidden(D_32, k2_tarski(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.34/1.64  tff(c_1544, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_1511, c_46])).
% 3.34/1.64  tff(c_1548, plain, $false, inference(negUnitSimplification, [status(thm)], [c_86, c_84, c_1544])).
% 3.34/1.64  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.34/1.64  
% 3.34/1.64  Inference rules
% 3.34/1.64  ----------------------
% 3.34/1.64  #Ref     : 0
% 3.34/1.64  #Sup     : 364
% 3.34/1.64  #Fact    : 0
% 3.34/1.64  #Define  : 0
% 3.34/1.64  #Split   : 0
% 3.34/1.64  #Chain   : 0
% 3.34/1.64  #Close   : 0
% 3.34/1.64  
% 3.34/1.64  Ordering : KBO
% 3.34/1.64  
% 3.34/1.64  Simplification rules
% 3.34/1.64  ----------------------
% 3.34/1.64  #Subsume      : 9
% 3.34/1.64  #Demod        : 189
% 3.34/1.64  #Tautology    : 266
% 3.34/1.64  #SimpNegUnit  : 1
% 3.34/1.64  #BackRed      : 0
% 3.34/1.64  
% 3.34/1.64  #Partial instantiations: 0
% 3.34/1.64  #Strategies tried      : 1
% 3.34/1.64  
% 3.34/1.64  Timing (in seconds)
% 3.34/1.64  ----------------------
% 3.34/1.64  Preprocessing        : 0.39
% 3.34/1.64  Parsing              : 0.20
% 3.34/1.64  CNF conversion       : 0.03
% 3.34/1.64  Main loop            : 0.43
% 3.34/1.64  Inferencing          : 0.15
% 3.34/1.64  Reduction            : 0.17
% 3.34/1.64  Demodulation         : 0.13
% 3.34/1.64  BG Simplification    : 0.03
% 3.34/1.64  Subsumption          : 0.07
% 3.34/1.64  Abstraction          : 0.02
% 3.34/1.64  MUC search           : 0.00
% 3.34/1.64  Cooper               : 0.00
% 3.34/1.64  Total                : 0.85
% 3.34/1.64  Index Insertion      : 0.00
% 3.34/1.64  Index Deletion       : 0.00
% 3.34/1.64  Index Matching       : 0.00
% 3.34/1.64  BG Taut test         : 0.00
%------------------------------------------------------------------------------

%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:51:30 EST 2020

% Result     : Theorem 3.44s
% Output     : CNFRefutation 3.44s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 188 expanded)
%              Number of leaves         :   36 (  79 expanded)
%              Depth                    :   14
%              Number of atoms          :   63 ( 187 expanded)
%              Number of equality atoms :   45 ( 154 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

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

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_66,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_68,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_43,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_84,negated_conjecture,(
    ~ ! [A,B] : k2_xboole_0(k1_tarski(A),B) != k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t49_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t94_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_39,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d5_xboole_0)).

tff(c_58,plain,(
    ! [A_27] : k2_tarski(A_27,A_27) = k1_tarski(A_27) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_197,plain,(
    ! [A_73,B_74] : k1_enumset1(A_73,A_73,B_74) = k2_tarski(A_73,B_74) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_36,plain,(
    ! [E_26,A_20,B_21] : r2_hidden(E_26,k1_enumset1(A_20,B_21,E_26)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_265,plain,(
    ! [B_76,A_77] : r2_hidden(B_76,k2_tarski(A_77,B_76)) ),
    inference(superposition,[status(thm),theory(equality)],[c_197,c_36])).

tff(c_268,plain,(
    ! [A_27] : r2_hidden(A_27,k1_tarski(A_27)) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_265])).

tff(c_26,plain,(
    ! [A_13] : k5_xboole_0(A_13,k1_xboole_0) = A_13 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_74,plain,(
    k2_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_306,plain,(
    ! [A_87,B_88] : k5_xboole_0(A_87,k3_xboole_0(A_87,B_88)) = k4_xboole_0(A_87,B_88) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_323,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k3_xboole_0(B_2,A_1)) = k4_xboole_0(A_1,B_2) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_306])).

tff(c_751,plain,(
    ! [A_108,B_109] : k5_xboole_0(k5_xboole_0(A_108,B_109),k3_xboole_0(A_108,B_109)) = k2_xboole_0(A_108,B_109) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_28,plain,(
    ! [A_14,B_15,C_16] : k5_xboole_0(k5_xboole_0(A_14,B_15),C_16) = k5_xboole_0(A_14,k5_xboole_0(B_15,C_16)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_772,plain,(
    ! [A_108,B_109] : k5_xboole_0(A_108,k5_xboole_0(B_109,k3_xboole_0(A_108,B_109))) = k2_xboole_0(A_108,B_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_751,c_28])).

tff(c_1319,plain,(
    ! [A_141,B_142] : k5_xboole_0(A_141,k4_xboole_0(B_142,A_141)) = k2_xboole_0(A_141,B_142) ),
    inference(demodulation,[status(thm),theory(equality)],[c_323,c_772])).

tff(c_150,plain,(
    ! [B_71,A_72] : k5_xboole_0(B_71,A_72) = k5_xboole_0(A_72,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_166,plain,(
    ! [A_72] : k5_xboole_0(k1_xboole_0,A_72) = A_72 ),
    inference(superposition,[status(thm),theory(equality)],[c_150,c_26])).

tff(c_30,plain,(
    ! [A_17] : k5_xboole_0(A_17,A_17) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_412,plain,(
    ! [A_99,B_100,C_101] : k5_xboole_0(k5_xboole_0(A_99,B_100),C_101) = k5_xboole_0(A_99,k5_xboole_0(B_100,C_101)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_487,plain,(
    ! [A_17,C_101] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_101)) = k5_xboole_0(k1_xboole_0,C_101) ),
    inference(superposition,[status(thm),theory(equality)],[c_30,c_412])).

tff(c_500,plain,(
    ! [A_17,C_101] : k5_xboole_0(A_17,k5_xboole_0(A_17,C_101)) = C_101 ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_487])).

tff(c_1462,plain,(
    ! [A_151,B_152] : k5_xboole_0(A_151,k2_xboole_0(A_151,B_152)) = k4_xboole_0(B_152,A_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_1319,c_500])).

tff(c_1514,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_xboole_0) = k4_xboole_0('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_74,c_1462])).

tff(c_1522,plain,(
    k4_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_tarski('#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_1514])).

tff(c_10,plain,(
    ! [D_10,A_5,B_6] :
      ( r2_hidden(D_10,A_5)
      | ~ r2_hidden(D_10,k4_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1540,plain,(
    ! [D_153] :
      ( r2_hidden(D_153,'#skF_6')
      | ~ r2_hidden(D_153,k1_tarski('#skF_5')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_1522,c_10])).

tff(c_1555,plain,(
    r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_268,c_1540])).

tff(c_24,plain,(
    ! [A_11,B_12] : k5_xboole_0(A_11,k3_xboole_0(A_11,B_12)) = k4_xboole_0(A_11,B_12) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_501,plain,(
    ! [A_102,C_103] : k5_xboole_0(A_102,k5_xboole_0(A_102,C_103)) = C_103 ),
    inference(demodulation,[status(thm),theory(equality)],[c_166,c_487])).

tff(c_1878,plain,(
    ! [A_166,B_167] : k5_xboole_0(A_166,k4_xboole_0(A_166,B_167)) = k3_xboole_0(A_166,B_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_24,c_501])).

tff(c_1923,plain,(
    k5_xboole_0('#skF_6',k1_tarski('#skF_5')) = k3_xboole_0('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1522,c_1878])).

tff(c_32,plain,(
    ! [A_18,B_19] : k5_xboole_0(k5_xboole_0(A_18,B_19),k3_xboole_0(A_18,B_19)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2013,plain,(
    k5_xboole_0(k3_xboole_0('#skF_6',k1_tarski('#skF_5')),k3_xboole_0('#skF_6',k1_tarski('#skF_5'))) = k2_xboole_0('#skF_6',k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1923,c_32])).

tff(c_2028,plain,(
    k2_xboole_0('#skF_6',k1_tarski('#skF_5')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_30,c_2013])).

tff(c_1337,plain,(
    ! [A_141,B_142] : k5_xboole_0(A_141,k2_xboole_0(A_141,B_142)) = k4_xboole_0(B_142,A_141) ),
    inference(superposition,[status(thm),theory(equality)],[c_1319,c_500])).

tff(c_2033,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = k5_xboole_0('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_2028,c_1337])).

tff(c_2036,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),'#skF_6') = '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_2033])).

tff(c_8,plain,(
    ! [D_10,B_6,A_5] :
      ( ~ r2_hidden(D_10,B_6)
      | ~ r2_hidden(D_10,k4_xboole_0(A_5,B_6)) ) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_2062,plain,(
    ! [D_169] :
      ( ~ r2_hidden(D_169,'#skF_6')
      | ~ r2_hidden(D_169,'#skF_6') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_2036,c_8])).

tff(c_2064,plain,(
    ~ r2_hidden('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_1555,c_2062])).

tff(c_2072,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_1555,c_2064])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 13:56:14 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.44/1.60  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.60  
% 3.44/1.60  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.60  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_6 > #skF_2 > #skF_4 > #skF_3
% 3.44/1.60  
% 3.44/1.60  %Foreground sorts:
% 3.44/1.60  
% 3.44/1.60  
% 3.44/1.60  %Background operators:
% 3.44/1.60  
% 3.44/1.60  
% 3.44/1.60  %Foreground operators:
% 3.44/1.60  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 3.44/1.60  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.44/1.60  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.44/1.60  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.44/1.60  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.44/1.60  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.44/1.60  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.44/1.60  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.44/1.60  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.44/1.60  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.44/1.60  tff('#skF_5', type, '#skF_5': $i).
% 3.44/1.60  tff('#skF_6', type, '#skF_6': $i).
% 3.44/1.60  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.44/1.60  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 3.44/1.60  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.60  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.44/1.60  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.60  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.44/1.60  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.44/1.60  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.44/1.60  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.44/1.60  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.44/1.60  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.44/1.60  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.44/1.60  
% 3.44/1.62  tff(f_66, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 3.44/1.62  tff(f_68, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.44/1.62  tff(f_64, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.44/1.62  tff(f_43, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.44/1.62  tff(f_84, negated_conjecture, ~(![A, B]: ~(k2_xboole_0(k1_tarski(A), B) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t49_zfmisc_1)).
% 3.44/1.62  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.44/1.62  tff(f_41, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.44/1.62  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t94_xboole_1)).
% 3.44/1.62  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.44/1.62  tff(f_29, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.44/1.62  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.44/1.62  tff(f_39, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d5_xboole_0)).
% 3.44/1.62  tff(c_58, plain, (![A_27]: (k2_tarski(A_27, A_27)=k1_tarski(A_27))), inference(cnfTransformation, [status(thm)], [f_66])).
% 3.44/1.62  tff(c_197, plain, (![A_73, B_74]: (k1_enumset1(A_73, A_73, B_74)=k2_tarski(A_73, B_74))), inference(cnfTransformation, [status(thm)], [f_68])).
% 3.44/1.62  tff(c_36, plain, (![E_26, A_20, B_21]: (r2_hidden(E_26, k1_enumset1(A_20, B_21, E_26)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.44/1.62  tff(c_265, plain, (![B_76, A_77]: (r2_hidden(B_76, k2_tarski(A_77, B_76)))), inference(superposition, [status(thm), theory('equality')], [c_197, c_36])).
% 3.44/1.62  tff(c_268, plain, (![A_27]: (r2_hidden(A_27, k1_tarski(A_27)))), inference(superposition, [status(thm), theory('equality')], [c_58, c_265])).
% 3.44/1.62  tff(c_26, plain, (![A_13]: (k5_xboole_0(A_13, k1_xboole_0)=A_13)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.44/1.62  tff(c_74, plain, (k2_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.44/1.62  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.44/1.62  tff(c_306, plain, (![A_87, B_88]: (k5_xboole_0(A_87, k3_xboole_0(A_87, B_88))=k4_xboole_0(A_87, B_88))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.44/1.62  tff(c_323, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k3_xboole_0(B_2, A_1))=k4_xboole_0(A_1, B_2))), inference(superposition, [status(thm), theory('equality')], [c_2, c_306])).
% 3.44/1.62  tff(c_751, plain, (![A_108, B_109]: (k5_xboole_0(k5_xboole_0(A_108, B_109), k3_xboole_0(A_108, B_109))=k2_xboole_0(A_108, B_109))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.44/1.62  tff(c_28, plain, (![A_14, B_15, C_16]: (k5_xboole_0(k5_xboole_0(A_14, B_15), C_16)=k5_xboole_0(A_14, k5_xboole_0(B_15, C_16)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.44/1.62  tff(c_772, plain, (![A_108, B_109]: (k5_xboole_0(A_108, k5_xboole_0(B_109, k3_xboole_0(A_108, B_109)))=k2_xboole_0(A_108, B_109))), inference(superposition, [status(thm), theory('equality')], [c_751, c_28])).
% 3.44/1.62  tff(c_1319, plain, (![A_141, B_142]: (k5_xboole_0(A_141, k4_xboole_0(B_142, A_141))=k2_xboole_0(A_141, B_142))), inference(demodulation, [status(thm), theory('equality')], [c_323, c_772])).
% 3.44/1.62  tff(c_150, plain, (![B_71, A_72]: (k5_xboole_0(B_71, A_72)=k5_xboole_0(A_72, B_71))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.44/1.62  tff(c_166, plain, (![A_72]: (k5_xboole_0(k1_xboole_0, A_72)=A_72)), inference(superposition, [status(thm), theory('equality')], [c_150, c_26])).
% 3.44/1.62  tff(c_30, plain, (![A_17]: (k5_xboole_0(A_17, A_17)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.44/1.62  tff(c_412, plain, (![A_99, B_100, C_101]: (k5_xboole_0(k5_xboole_0(A_99, B_100), C_101)=k5_xboole_0(A_99, k5_xboole_0(B_100, C_101)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.44/1.62  tff(c_487, plain, (![A_17, C_101]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_101))=k5_xboole_0(k1_xboole_0, C_101))), inference(superposition, [status(thm), theory('equality')], [c_30, c_412])).
% 3.44/1.62  tff(c_500, plain, (![A_17, C_101]: (k5_xboole_0(A_17, k5_xboole_0(A_17, C_101))=C_101)), inference(demodulation, [status(thm), theory('equality')], [c_166, c_487])).
% 3.44/1.62  tff(c_1462, plain, (![A_151, B_152]: (k5_xboole_0(A_151, k2_xboole_0(A_151, B_152))=k4_xboole_0(B_152, A_151))), inference(superposition, [status(thm), theory('equality')], [c_1319, c_500])).
% 3.44/1.62  tff(c_1514, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_xboole_0)=k4_xboole_0('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_74, c_1462])).
% 3.44/1.62  tff(c_1522, plain, (k4_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_tarski('#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_26, c_1514])).
% 3.44/1.62  tff(c_10, plain, (![D_10, A_5, B_6]: (r2_hidden(D_10, A_5) | ~r2_hidden(D_10, k4_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.44/1.62  tff(c_1540, plain, (![D_153]: (r2_hidden(D_153, '#skF_6') | ~r2_hidden(D_153, k1_tarski('#skF_5')))), inference(superposition, [status(thm), theory('equality')], [c_1522, c_10])).
% 3.44/1.62  tff(c_1555, plain, (r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_268, c_1540])).
% 3.44/1.62  tff(c_24, plain, (![A_11, B_12]: (k5_xboole_0(A_11, k3_xboole_0(A_11, B_12))=k4_xboole_0(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.44/1.62  tff(c_501, plain, (![A_102, C_103]: (k5_xboole_0(A_102, k5_xboole_0(A_102, C_103))=C_103)), inference(demodulation, [status(thm), theory('equality')], [c_166, c_487])).
% 3.44/1.62  tff(c_1878, plain, (![A_166, B_167]: (k5_xboole_0(A_166, k4_xboole_0(A_166, B_167))=k3_xboole_0(A_166, B_167))), inference(superposition, [status(thm), theory('equality')], [c_24, c_501])).
% 3.44/1.62  tff(c_1923, plain, (k5_xboole_0('#skF_6', k1_tarski('#skF_5'))=k3_xboole_0('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1522, c_1878])).
% 3.44/1.62  tff(c_32, plain, (![A_18, B_19]: (k5_xboole_0(k5_xboole_0(A_18, B_19), k3_xboole_0(A_18, B_19))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.44/1.62  tff(c_2013, plain, (k5_xboole_0(k3_xboole_0('#skF_6', k1_tarski('#skF_5')), k3_xboole_0('#skF_6', k1_tarski('#skF_5')))=k2_xboole_0('#skF_6', k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_1923, c_32])).
% 3.44/1.62  tff(c_2028, plain, (k2_xboole_0('#skF_6', k1_tarski('#skF_5'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_30, c_2013])).
% 3.44/1.62  tff(c_1337, plain, (![A_141, B_142]: (k5_xboole_0(A_141, k2_xboole_0(A_141, B_142))=k4_xboole_0(B_142, A_141))), inference(superposition, [status(thm), theory('equality')], [c_1319, c_500])).
% 3.44/1.62  tff(c_2033, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')=k5_xboole_0('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_2028, c_1337])).
% 3.44/1.62  tff(c_2036, plain, (k4_xboole_0(k1_tarski('#skF_5'), '#skF_6')='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_26, c_2033])).
% 3.44/1.62  tff(c_8, plain, (![D_10, B_6, A_5]: (~r2_hidden(D_10, B_6) | ~r2_hidden(D_10, k4_xboole_0(A_5, B_6)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.44/1.62  tff(c_2062, plain, (![D_169]: (~r2_hidden(D_169, '#skF_6') | ~r2_hidden(D_169, '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_2036, c_8])).
% 3.44/1.62  tff(c_2064, plain, (~r2_hidden('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_1555, c_2062])).
% 3.44/1.62  tff(c_2072, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_1555, c_2064])).
% 3.44/1.62  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.44/1.62  
% 3.44/1.62  Inference rules
% 3.44/1.62  ----------------------
% 3.44/1.62  #Ref     : 0
% 3.44/1.62  #Sup     : 504
% 3.44/1.62  #Fact    : 0
% 3.44/1.62  #Define  : 0
% 3.44/1.62  #Split   : 0
% 3.44/1.62  #Chain   : 0
% 3.44/1.62  #Close   : 0
% 3.44/1.62  
% 3.44/1.62  Ordering : KBO
% 3.44/1.62  
% 3.44/1.62  Simplification rules
% 3.44/1.62  ----------------------
% 3.44/1.62  #Subsume      : 16
% 3.44/1.62  #Demod        : 200
% 3.44/1.62  #Tautology    : 282
% 3.44/1.62  #SimpNegUnit  : 0
% 3.44/1.62  #BackRed      : 1
% 3.44/1.62  
% 3.44/1.62  #Partial instantiations: 0
% 3.44/1.62  #Strategies tried      : 1
% 3.44/1.62  
% 3.44/1.62  Timing (in seconds)
% 3.44/1.62  ----------------------
% 3.44/1.62  Preprocessing        : 0.32
% 3.44/1.62  Parsing              : 0.16
% 3.44/1.62  CNF conversion       : 0.03
% 3.44/1.62  Main loop            : 0.51
% 3.44/1.62  Inferencing          : 0.17
% 3.44/1.62  Reduction            : 0.20
% 3.44/1.62  Demodulation         : 0.18
% 3.44/1.62  BG Simplification    : 0.03
% 3.44/1.62  Subsumption          : 0.08
% 3.44/1.62  Abstraction          : 0.03
% 3.44/1.62  MUC search           : 0.00
% 3.44/1.62  Cooper               : 0.00
% 3.44/1.62  Total                : 0.86
% 3.44/1.62  Index Insertion      : 0.00
% 3.44/1.62  Index Deletion       : 0.00
% 3.44/1.62  Index Matching       : 0.00
% 3.44/1.62  BG Taut test         : 0.00
%------------------------------------------------------------------------------

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
% DateTime   : Thu Dec  3 09:50:14 EST 2020

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   93 ( 229 expanded)
%              Number of leaves         :   33 (  91 expanded)
%              Depth                    :   15
%              Number of atoms          :   97 ( 334 expanded)
%              Number of equality atoms :   82 ( 316 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

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

tff(f_100,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_79,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_51,axiom,(
    ! [A,B] : r1_tarski(k4_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t36_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_55,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(c_54,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_98,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_54])).

tff(c_52,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_88,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_52])).

tff(c_58,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_104,plain,(
    ! [A_66,B_67] : r1_tarski(A_66,k2_xboole_0(A_66,B_67)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_107,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_104])).

tff(c_414,plain,(
    ! [B_94,A_95] :
      ( k1_tarski(B_94) = A_95
      | k1_xboole_0 = A_95
      | ~ r1_tarski(A_95,k1_tarski(B_94)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_421,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_107,c_414])).

tff(c_435,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_88,c_421])).

tff(c_436,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_437,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_54])).

tff(c_26,plain,(
    ! [A_23] : k5_xboole_0(A_23,A_23) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_438,plain,(
    ! [A_23] : k5_xboole_0(A_23,A_23) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_437,c_26])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_591,plain,(
    ! [A_117,B_118] : k5_xboole_0(A_117,k3_xboole_0(A_117,B_118)) = k4_xboole_0(A_117,B_118) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_600,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_591])).

tff(c_604,plain,(
    ! [A_119] : k4_xboole_0(A_119,A_119) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_438,c_600])).

tff(c_20,plain,(
    ! [A_16,B_17] : r1_tarski(k4_xboole_0(A_16,B_17),A_16) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_508,plain,(
    ! [A_106,B_107] :
      ( k2_xboole_0(A_106,B_107) = B_107
      | ~ r1_tarski(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_522,plain,(
    ! [A_16,B_17] : k2_xboole_0(k4_xboole_0(A_16,B_17),A_16) = A_16 ),
    inference(resolution,[status(thm)],[c_20,c_508])).

tff(c_609,plain,(
    ! [A_119] : k2_xboole_0('#skF_2',A_119) = A_119 ),
    inference(superposition,[status(thm),theory(equality)],[c_604,c_522])).

tff(c_636,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_609,c_58])).

tff(c_638,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_436,c_636])).

tff(c_639,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_640,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_52])).

tff(c_56,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_100])).

tff(c_673,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_640,c_56])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_1106,plain,(
    ! [A_163,B_164] : k5_xboole_0(k5_xboole_0(A_163,B_164),k2_xboole_0(A_163,B_164)) = k3_xboole_0(A_163,B_164) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1154,plain,(
    ! [A_3] : k5_xboole_0(k5_xboole_0(A_3,A_3),A_3) = k3_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_1106])).

tff(c_1236,plain,(
    ! [A_168] : k5_xboole_0(k1_xboole_0,A_168) = A_168 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6,c_1154])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1252,plain,(
    ! [A_168] : k5_xboole_0(A_168,k1_xboole_0) = A_168 ),
    inference(superposition,[status(thm),theory(equality)],[c_1236,c_2])).

tff(c_985,plain,(
    ! [B_155,A_156] :
      ( k1_tarski(B_155) = A_156
      | k1_xboole_0 = A_156
      | ~ r1_tarski(A_156,k1_tarski(B_155)) ) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_996,plain,(
    ! [A_156] :
      ( k1_tarski('#skF_1') = A_156
      | k1_xboole_0 = A_156
      | ~ r1_tarski(A_156,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_985])).

tff(c_1007,plain,(
    ! [A_157] :
      ( A_157 = '#skF_2'
      | k1_xboole_0 = A_157
      | ~ r1_tarski(A_157,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_996])).

tff(c_1024,plain,(
    ! [B_17] :
      ( k4_xboole_0('#skF_2',B_17) = '#skF_2'
      | k4_xboole_0('#skF_2',B_17) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_20,c_1007])).

tff(c_14,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_657,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_640,c_58])).

tff(c_1151,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_3'),'#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_657,c_1106])).

tff(c_1161,plain,(
    k5_xboole_0('#skF_2',k5_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_1151])).

tff(c_1162,plain,(
    ! [A_3] : k5_xboole_0(k1_xboole_0,A_3) = A_3 ),
    inference(demodulation,[status(thm),theory(equality)],[c_26,c_6,c_1154])).

tff(c_1164,plain,(
    ! [A_165,B_166,C_167] : k5_xboole_0(k5_xboole_0(A_165,B_166),C_167) = k5_xboole_0(A_165,k5_xboole_0(B_166,C_167)) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1227,plain,(
    ! [A_23,C_167] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_167)) = k5_xboole_0(k1_xboole_0,C_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1164])).

tff(c_1576,plain,(
    ! [A_177,C_178] : k5_xboole_0(A_177,k5_xboole_0(A_177,C_178)) = C_178 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1162,c_1227])).

tff(c_1632,plain,(
    k5_xboole_0('#skF_2',k3_xboole_0('#skF_2','#skF_3')) = k5_xboole_0('#skF_3','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_1161,c_1576])).

tff(c_1676,plain,(
    k5_xboole_0('#skF_3','#skF_2') = k4_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_1632])).

tff(c_1575,plain,(
    ! [A_23,C_167] : k5_xboole_0(A_23,k5_xboole_0(A_23,C_167)) = C_167 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1162,c_1227])).

tff(c_1788,plain,(
    k5_xboole_0('#skF_3',k4_xboole_0('#skF_2','#skF_3')) = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1676,c_1575])).

tff(c_1831,plain,
    ( k5_xboole_0('#skF_3',k1_xboole_0) = '#skF_2'
    | k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(superposition,[status(thm),theory(equality)],[c_1024,c_1788])).

tff(c_1835,plain,
    ( '#skF_2' = '#skF_3'
    | k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1252,c_1831])).

tff(c_1836,plain,(
    k4_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(negUnitSimplification,[status(thm)],[c_673,c_1835])).

tff(c_1838,plain,(
    k5_xboole_0('#skF_3','#skF_2') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1836,c_1676])).

tff(c_1231,plain,(
    ! [A_165,B_166] : k5_xboole_0(A_165,k5_xboole_0(B_166,k5_xboole_0(A_165,B_166))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_26,c_1164])).

tff(c_1622,plain,(
    ! [B_166,A_165] : k5_xboole_0(B_166,k5_xboole_0(A_165,B_166)) = k5_xboole_0(A_165,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1231,c_1576])).

tff(c_1673,plain,(
    ! [B_166,A_165] : k5_xboole_0(B_166,k5_xboole_0(A_165,B_166)) = A_165 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1252,c_1622])).

tff(c_1870,plain,(
    k5_xboole_0('#skF_2','#skF_2') = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1838,c_1673])).

tff(c_1905,plain,(
    k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1870,c_26])).

tff(c_1913,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_639,c_1905])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.12  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n020.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 17:21:07 EST 2020
% 0.13/0.33  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.50  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.51  
% 3.18/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.51  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.18/1.51  
% 3.18/1.51  %Foreground sorts:
% 3.18/1.51  
% 3.18/1.51  
% 3.18/1.51  %Background operators:
% 3.18/1.51  
% 3.18/1.51  
% 3.18/1.51  %Foreground operators:
% 3.18/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.18/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.18/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.18/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.18/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.18/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.18/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.18/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.18/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.18/1.51  tff('#skF_2', type, '#skF_2': $i).
% 3.18/1.51  tff('#skF_3', type, '#skF_3': $i).
% 3.18/1.51  tff('#skF_1', type, '#skF_1': $i).
% 3.18/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.18/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.18/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.18/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.51  
% 3.18/1.53  tff(f_100, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.18/1.53  tff(f_53, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.18/1.53  tff(f_79, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.18/1.53  tff(f_57, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.18/1.53  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.18/1.53  tff(f_39, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.18/1.53  tff(f_51, axiom, (![A, B]: r1_tarski(k4_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t36_xboole_1)).
% 3.18/1.53  tff(f_49, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.18/1.53  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.18/1.53  tff(f_59, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.18/1.53  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.18/1.53  tff(f_55, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.18/1.53  tff(c_54, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.18/1.53  tff(c_98, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_54])).
% 3.18/1.53  tff(c_52, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.18/1.53  tff(c_88, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_52])).
% 3.18/1.53  tff(c_58, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.18/1.53  tff(c_104, plain, (![A_66, B_67]: (r1_tarski(A_66, k2_xboole_0(A_66, B_67)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 3.18/1.53  tff(c_107, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_104])).
% 3.18/1.53  tff(c_414, plain, (![B_94, A_95]: (k1_tarski(B_94)=A_95 | k1_xboole_0=A_95 | ~r1_tarski(A_95, k1_tarski(B_94)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.18/1.53  tff(c_421, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_107, c_414])).
% 3.18/1.53  tff(c_435, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_88, c_421])).
% 3.18/1.53  tff(c_436, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_54])).
% 3.18/1.53  tff(c_437, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_54])).
% 3.18/1.53  tff(c_26, plain, (![A_23]: (k5_xboole_0(A_23, A_23)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.18/1.53  tff(c_438, plain, (![A_23]: (k5_xboole_0(A_23, A_23)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_437, c_26])).
% 3.18/1.53  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.18/1.53  tff(c_591, plain, (![A_117, B_118]: (k5_xboole_0(A_117, k3_xboole_0(A_117, B_118))=k4_xboole_0(A_117, B_118))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.18/1.53  tff(c_600, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_591])).
% 3.18/1.53  tff(c_604, plain, (![A_119]: (k4_xboole_0(A_119, A_119)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_438, c_600])).
% 3.18/1.53  tff(c_20, plain, (![A_16, B_17]: (r1_tarski(k4_xboole_0(A_16, B_17), A_16))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.18/1.53  tff(c_508, plain, (![A_106, B_107]: (k2_xboole_0(A_106, B_107)=B_107 | ~r1_tarski(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.18/1.53  tff(c_522, plain, (![A_16, B_17]: (k2_xboole_0(k4_xboole_0(A_16, B_17), A_16)=A_16)), inference(resolution, [status(thm)], [c_20, c_508])).
% 3.18/1.53  tff(c_609, plain, (![A_119]: (k2_xboole_0('#skF_2', A_119)=A_119)), inference(superposition, [status(thm), theory('equality')], [c_604, c_522])).
% 3.18/1.53  tff(c_636, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_609, c_58])).
% 3.18/1.53  tff(c_638, plain, $false, inference(negUnitSimplification, [status(thm)], [c_436, c_636])).
% 3.18/1.53  tff(c_639, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_52])).
% 3.18/1.53  tff(c_640, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_52])).
% 3.18/1.53  tff(c_56, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_100])).
% 3.18/1.53  tff(c_673, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_640, c_640, c_56])).
% 3.18/1.53  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.18/1.53  tff(c_1106, plain, (![A_163, B_164]: (k5_xboole_0(k5_xboole_0(A_163, B_164), k2_xboole_0(A_163, B_164))=k3_xboole_0(A_163, B_164))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.18/1.53  tff(c_1154, plain, (![A_3]: (k5_xboole_0(k5_xboole_0(A_3, A_3), A_3)=k3_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_1106])).
% 3.18/1.53  tff(c_1236, plain, (![A_168]: (k5_xboole_0(k1_xboole_0, A_168)=A_168)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6, c_1154])).
% 3.18/1.53  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.18/1.53  tff(c_1252, plain, (![A_168]: (k5_xboole_0(A_168, k1_xboole_0)=A_168)), inference(superposition, [status(thm), theory('equality')], [c_1236, c_2])).
% 3.18/1.53  tff(c_985, plain, (![B_155, A_156]: (k1_tarski(B_155)=A_156 | k1_xboole_0=A_156 | ~r1_tarski(A_156, k1_tarski(B_155)))), inference(cnfTransformation, [status(thm)], [f_79])).
% 3.18/1.53  tff(c_996, plain, (![A_156]: (k1_tarski('#skF_1')=A_156 | k1_xboole_0=A_156 | ~r1_tarski(A_156, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_640, c_985])).
% 3.18/1.53  tff(c_1007, plain, (![A_157]: (A_157='#skF_2' | k1_xboole_0=A_157 | ~r1_tarski(A_157, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_640, c_996])).
% 3.18/1.53  tff(c_1024, plain, (![B_17]: (k4_xboole_0('#skF_2', B_17)='#skF_2' | k4_xboole_0('#skF_2', B_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_1007])).
% 3.18/1.53  tff(c_14, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.18/1.53  tff(c_657, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_640, c_58])).
% 3.18/1.53  tff(c_1151, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_3'), '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_657, c_1106])).
% 3.18/1.53  tff(c_1161, plain, (k5_xboole_0('#skF_2', k5_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_1151])).
% 3.18/1.53  tff(c_1162, plain, (![A_3]: (k5_xboole_0(k1_xboole_0, A_3)=A_3)), inference(demodulation, [status(thm), theory('equality')], [c_26, c_6, c_1154])).
% 3.18/1.53  tff(c_1164, plain, (![A_165, B_166, C_167]: (k5_xboole_0(k5_xboole_0(A_165, B_166), C_167)=k5_xboole_0(A_165, k5_xboole_0(B_166, C_167)))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.18/1.53  tff(c_1227, plain, (![A_23, C_167]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_167))=k5_xboole_0(k1_xboole_0, C_167))), inference(superposition, [status(thm), theory('equality')], [c_26, c_1164])).
% 3.18/1.53  tff(c_1576, plain, (![A_177, C_178]: (k5_xboole_0(A_177, k5_xboole_0(A_177, C_178))=C_178)), inference(demodulation, [status(thm), theory('equality')], [c_1162, c_1227])).
% 3.18/1.53  tff(c_1632, plain, (k5_xboole_0('#skF_2', k3_xboole_0('#skF_2', '#skF_3'))=k5_xboole_0('#skF_3', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_1161, c_1576])).
% 3.18/1.53  tff(c_1676, plain, (k5_xboole_0('#skF_3', '#skF_2')=k4_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_14, c_1632])).
% 3.18/1.53  tff(c_1575, plain, (![A_23, C_167]: (k5_xboole_0(A_23, k5_xboole_0(A_23, C_167))=C_167)), inference(demodulation, [status(thm), theory('equality')], [c_1162, c_1227])).
% 3.18/1.53  tff(c_1788, plain, (k5_xboole_0('#skF_3', k4_xboole_0('#skF_2', '#skF_3'))='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1676, c_1575])).
% 3.18/1.53  tff(c_1831, plain, (k5_xboole_0('#skF_3', k1_xboole_0)='#skF_2' | k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(superposition, [status(thm), theory('equality')], [c_1024, c_1788])).
% 3.18/1.53  tff(c_1835, plain, ('#skF_2'='#skF_3' | k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1252, c_1831])).
% 3.18/1.53  tff(c_1836, plain, (k4_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(negUnitSimplification, [status(thm)], [c_673, c_1835])).
% 3.18/1.53  tff(c_1838, plain, (k5_xboole_0('#skF_3', '#skF_2')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_1836, c_1676])).
% 3.18/1.53  tff(c_1231, plain, (![A_165, B_166]: (k5_xboole_0(A_165, k5_xboole_0(B_166, k5_xboole_0(A_165, B_166)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_26, c_1164])).
% 3.18/1.53  tff(c_1622, plain, (![B_166, A_165]: (k5_xboole_0(B_166, k5_xboole_0(A_165, B_166))=k5_xboole_0(A_165, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1231, c_1576])).
% 3.18/1.53  tff(c_1673, plain, (![B_166, A_165]: (k5_xboole_0(B_166, k5_xboole_0(A_165, B_166))=A_165)), inference(demodulation, [status(thm), theory('equality')], [c_1252, c_1622])).
% 3.18/1.53  tff(c_1870, plain, (k5_xboole_0('#skF_2', '#skF_2')='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1838, c_1673])).
% 3.18/1.53  tff(c_1905, plain, (k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1870, c_26])).
% 3.18/1.53  tff(c_1913, plain, $false, inference(negUnitSimplification, [status(thm)], [c_639, c_1905])).
% 3.18/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.18/1.53  
% 3.18/1.53  Inference rules
% 3.18/1.53  ----------------------
% 3.18/1.53  #Ref     : 0
% 3.18/1.53  #Sup     : 451
% 3.18/1.53  #Fact    : 1
% 3.18/1.53  #Define  : 0
% 3.18/1.53  #Split   : 3
% 3.18/1.53  #Chain   : 0
% 3.18/1.53  #Close   : 0
% 3.18/1.53  
% 3.18/1.53  Ordering : KBO
% 3.18/1.53  
% 3.18/1.53  Simplification rules
% 3.18/1.53  ----------------------
% 3.18/1.53  #Subsume      : 13
% 3.18/1.53  #Demod        : 224
% 3.18/1.53  #Tautology    : 304
% 3.18/1.53  #SimpNegUnit  : 12
% 3.18/1.53  #BackRed      : 9
% 3.18/1.53  
% 3.18/1.53  #Partial instantiations: 0
% 3.18/1.53  #Strategies tried      : 1
% 3.18/1.53  
% 3.18/1.53  Timing (in seconds)
% 3.18/1.53  ----------------------
% 3.37/1.53  Preprocessing        : 0.32
% 3.37/1.53  Parsing              : 0.17
% 3.37/1.53  CNF conversion       : 0.02
% 3.37/1.53  Main loop            : 0.46
% 3.37/1.53  Inferencing          : 0.16
% 3.37/1.53  Reduction            : 0.17
% 3.37/1.53  Demodulation         : 0.14
% 3.37/1.53  BG Simplification    : 0.02
% 3.37/1.53  Subsumption          : 0.07
% 3.37/1.53  Abstraction          : 0.02
% 3.37/1.53  MUC search           : 0.00
% 3.37/1.53  Cooper               : 0.00
% 3.37/1.53  Total                : 0.82
% 3.37/1.53  Index Insertion      : 0.00
% 3.37/1.53  Index Deletion       : 0.00
% 3.37/1.53  Index Matching       : 0.00
% 3.37/1.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------

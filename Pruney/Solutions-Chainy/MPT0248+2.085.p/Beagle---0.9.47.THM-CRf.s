%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n008.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:16 EST 2020

% Result     : Theorem 3.24s
% Output     : CNFRefutation 3.41s
% Verified   : 
% Statistics : Number of formulae       :   90 ( 187 expanded)
%              Number of leaves         :   32 (  74 expanded)
%              Depth                    :    9
%              Number of atoms          :  105 ( 345 expanded)
%              Number of equality atoms :   78 ( 315 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   1 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_57,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_59,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ( ~ ( ~ r1_xboole_0(A,A)
          & A = k1_xboole_0 )
      & ~ ( A != k1_xboole_0
          & r1_xboole_0(A,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t66_xboole_1)).

tff(f_55,axiom,(
    ! [A,B,C] :
      ( ( r1_tarski(A,B)
        & r1_tarski(A,C)
        & r1_xboole_0(B,C) )
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t67_xboole_1)).

tff(c_50,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_113,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_50])).

tff(c_48,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_114,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_48])).

tff(c_54,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_122,plain,(
    ! [A_62,B_63] : r1_tarski(A_62,k2_xboole_0(A_62,B_63)) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_125,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_122])).

tff(c_273,plain,(
    ! [B_78,A_79] :
      ( k1_tarski(B_78) = A_79
      | k1_xboole_0 = A_79
      | ~ r1_tarski(A_79,k1_tarski(B_78)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_276,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_125,c_273])).

tff(c_291,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_113,c_114,c_276])).

tff(c_292,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_293,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_48])).

tff(c_52,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_320,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_293,c_52])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_328,plain,(
    ! [B_86,A_87] : k5_xboole_0(B_86,A_87) = k5_xboole_0(A_87,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_344,plain,(
    ! [A_87] : k5_xboole_0(k1_xboole_0,A_87) = A_87 ),
    inference(superposition,[status(thm),theory(equality)],[c_328,c_10])).

tff(c_22,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_676,plain,(
    ! [A_105,B_106,C_107] : k5_xboole_0(k5_xboole_0(A_105,B_106),C_107) = k5_xboole_0(A_105,k5_xboole_0(B_106,C_107)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_770,plain,(
    ! [A_19,C_107] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_107)) = k5_xboole_0(k1_xboole_0,C_107) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_676])).

tff(c_785,plain,(
    ! [A_108,C_109] : k5_xboole_0(A_108,k5_xboole_0(A_108,C_109)) = C_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_344,c_770])).

tff(c_843,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_785])).

tff(c_294,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_54])).

tff(c_543,plain,(
    ! [A_101,B_102] : k5_xboole_0(k5_xboole_0(A_101,B_102),k2_xboole_0(A_101,B_102)) = k3_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_579,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_3'),'#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_294,c_543])).

tff(c_591,plain,(
    k5_xboole_0('#skF_2',k5_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_579])).

tff(c_865,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_843,c_591])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_447,plain,(
    ! [B_93,A_94] :
      ( k1_tarski(B_93) = A_94
      | k1_xboole_0 = A_94
      | ~ r1_tarski(A_94,k1_tarski(B_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_458,plain,(
    ! [A_94] :
      ( k1_tarski('#skF_1') = A_94
      | k1_xboole_0 = A_94
      | ~ r1_tarski(A_94,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_293,c_447])).

tff(c_484,plain,(
    ! [A_96] :
      ( A_96 = '#skF_2'
      | k1_xboole_0 = A_96
      | ~ r1_tarski(A_96,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_293,c_458])).

tff(c_496,plain,(
    ! [B_8] :
      ( k3_xboole_0('#skF_2',B_8) = '#skF_2'
      | k3_xboole_0('#skF_2',B_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_484])).

tff(c_961,plain,
    ( k3_xboole_0('#skF_2','#skF_3') = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_865,c_496])).

tff(c_970,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_865,c_961])).

tff(c_972,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_292,c_320,c_970])).

tff(c_973,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_974,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_50])).

tff(c_975,plain,(
    ! [A_9] : k5_xboole_0(A_9,'#skF_2') = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_974,c_10])).

tff(c_12,plain,(
    r1_xboole_0(k1_xboole_0,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_978,plain,(
    r1_xboole_0('#skF_2','#skF_2') ),
    inference(demodulation,[status(thm),theory(equality)],[c_974,c_974,c_12])).

tff(c_16,plain,(
    ! [A_11,B_12,C_13] :
      ( k1_xboole_0 = A_11
      | ~ r1_xboole_0(B_12,C_13)
      | ~ r1_tarski(A_11,C_13)
      | ~ r1_tarski(A_11,B_12) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_1884,plain,(
    ! [A_153,B_154,C_155] :
      ( A_153 = '#skF_2'
      | ~ r1_xboole_0(B_154,C_155)
      | ~ r1_tarski(A_153,C_155)
      | ~ r1_tarski(A_153,B_154) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_974,c_16])).

tff(c_1888,plain,(
    ! [A_156] :
      ( A_156 = '#skF_2'
      | ~ r1_tarski(A_156,'#skF_2') ) ),
    inference(resolution,[status(thm)],[c_978,c_1884])).

tff(c_1897,plain,(
    ! [B_8] : k3_xboole_0('#skF_2',B_8) = '#skF_2' ),
    inference(resolution,[status(thm)],[c_8,c_1888])).

tff(c_1189,plain,(
    ! [A_134,B_135] : k5_xboole_0(k5_xboole_0(A_134,B_135),k2_xboole_0(A_134,B_135)) = k3_xboole_0(A_134,B_135) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_1231,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_3'),k1_tarski('#skF_1')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1189])).

tff(c_1238,plain,(
    k5_xboole_0('#skF_3',k1_tarski('#skF_1')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_975,c_2,c_1231])).

tff(c_1034,plain,(
    ! [B_121,A_122] : k5_xboole_0(B_121,A_122) = k5_xboole_0(A_122,B_121) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_1050,plain,(
    ! [A_122] : k5_xboole_0('#skF_2',A_122) = A_122 ),
    inference(superposition,[status(thm),theory(equality)],[c_1034,c_975])).

tff(c_976,plain,(
    ! [A_19] : k5_xboole_0(A_19,A_19) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_974,c_22])).

tff(c_1315,plain,(
    ! [A_138,B_139,C_140] : k5_xboole_0(k5_xboole_0(A_138,B_139),C_140) = k5_xboole_0(A_138,k5_xboole_0(B_139,C_140)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_1406,plain,(
    ! [A_19,C_140] : k5_xboole_0(A_19,k5_xboole_0(A_19,C_140)) = k5_xboole_0('#skF_2',C_140) ),
    inference(superposition,[status(thm),theory(equality)],[c_976,c_1315])).

tff(c_1420,plain,(
    ! [A_141,C_142] : k5_xboole_0(A_141,k5_xboole_0(A_141,C_142)) = C_142 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1050,c_1406])).

tff(c_1462,plain,(
    k5_xboole_0('#skF_3',k3_xboole_0('#skF_2','#skF_3')) = k1_tarski('#skF_1') ),
    inference(superposition,[status(thm),theory(equality)],[c_1238,c_1420])).

tff(c_1901,plain,(
    k5_xboole_0('#skF_3','#skF_2') = k1_tarski('#skF_1') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1897,c_1462])).

tff(c_1904,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_975,c_1901])).

tff(c_1906,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_973,c_1904])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n008.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 10:02:30 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.24/1.57  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.57  
% 3.41/1.57  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.57  %$ r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.41/1.57  
% 3.41/1.57  %Foreground sorts:
% 3.41/1.57  
% 3.41/1.57  
% 3.41/1.57  %Background operators:
% 3.41/1.57  
% 3.41/1.57  
% 3.41/1.57  %Foreground operators:
% 3.41/1.57  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.41/1.57  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.41/1.57  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.41/1.57  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.41/1.57  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.41/1.57  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.41/1.57  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.41/1.57  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.41/1.57  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.41/1.57  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.41/1.57  tff('#skF_2', type, '#skF_2': $i).
% 3.41/1.57  tff('#skF_3', type, '#skF_3': $i).
% 3.41/1.57  tff('#skF_1', type, '#skF_1': $i).
% 3.41/1.57  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.41/1.57  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.41/1.57  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.41/1.57  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.41/1.57  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.41/1.57  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.41/1.57  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.41/1.57  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.41/1.57  
% 3.41/1.59  tff(f_104, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.41/1.59  tff(f_57, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.41/1.59  tff(f_83, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.41/1.59  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.41/1.59  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 3.41/1.59  tff(f_61, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.41/1.59  tff(f_59, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.41/1.59  tff(f_63, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.41/1.59  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.41/1.59  tff(f_47, axiom, (![A]: (~(~r1_xboole_0(A, A) & (A = k1_xboole_0)) & ~(~(A = k1_xboole_0) & r1_xboole_0(A, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t66_xboole_1)).
% 3.41/1.59  tff(f_55, axiom, (![A, B, C]: (((r1_tarski(A, B) & r1_tarski(A, C)) & r1_xboole_0(B, C)) => (A = k1_xboole_0))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t67_xboole_1)).
% 3.41/1.59  tff(c_50, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.41/1.59  tff(c_113, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_50])).
% 3.41/1.59  tff(c_48, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.41/1.59  tff(c_114, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_48])).
% 3.41/1.59  tff(c_54, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.41/1.59  tff(c_122, plain, (![A_62, B_63]: (r1_tarski(A_62, k2_xboole_0(A_62, B_63)))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.41/1.59  tff(c_125, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_54, c_122])).
% 3.41/1.59  tff(c_273, plain, (![B_78, A_79]: (k1_tarski(B_78)=A_79 | k1_xboole_0=A_79 | ~r1_tarski(A_79, k1_tarski(B_78)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.41/1.59  tff(c_276, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_125, c_273])).
% 3.41/1.59  tff(c_291, plain, $false, inference(negUnitSimplification, [status(thm)], [c_113, c_114, c_276])).
% 3.41/1.59  tff(c_292, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_48])).
% 3.41/1.59  tff(c_293, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_48])).
% 3.41/1.59  tff(c_52, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.41/1.59  tff(c_320, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_293, c_293, c_52])).
% 3.41/1.59  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.41/1.59  tff(c_328, plain, (![B_86, A_87]: (k5_xboole_0(B_86, A_87)=k5_xboole_0(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.41/1.59  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.41/1.59  tff(c_344, plain, (![A_87]: (k5_xboole_0(k1_xboole_0, A_87)=A_87)), inference(superposition, [status(thm), theory('equality')], [c_328, c_10])).
% 3.41/1.59  tff(c_22, plain, (![A_19]: (k5_xboole_0(A_19, A_19)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.41/1.59  tff(c_676, plain, (![A_105, B_106, C_107]: (k5_xboole_0(k5_xboole_0(A_105, B_106), C_107)=k5_xboole_0(A_105, k5_xboole_0(B_106, C_107)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.41/1.59  tff(c_770, plain, (![A_19, C_107]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_107))=k5_xboole_0(k1_xboole_0, C_107))), inference(superposition, [status(thm), theory('equality')], [c_22, c_676])).
% 3.41/1.59  tff(c_785, plain, (![A_108, C_109]: (k5_xboole_0(A_108, k5_xboole_0(A_108, C_109))=C_109)), inference(demodulation, [status(thm), theory('equality')], [c_344, c_770])).
% 3.41/1.59  tff(c_843, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_785])).
% 3.41/1.59  tff(c_294, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_293, c_54])).
% 3.41/1.59  tff(c_543, plain, (![A_101, B_102]: (k5_xboole_0(k5_xboole_0(A_101, B_102), k2_xboole_0(A_101, B_102))=k3_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.41/1.59  tff(c_579, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_3'), '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_294, c_543])).
% 3.41/1.59  tff(c_591, plain, (k5_xboole_0('#skF_2', k5_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_579])).
% 3.41/1.59  tff(c_865, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_843, c_591])).
% 3.41/1.59  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.41/1.59  tff(c_447, plain, (![B_93, A_94]: (k1_tarski(B_93)=A_94 | k1_xboole_0=A_94 | ~r1_tarski(A_94, k1_tarski(B_93)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.41/1.59  tff(c_458, plain, (![A_94]: (k1_tarski('#skF_1')=A_94 | k1_xboole_0=A_94 | ~r1_tarski(A_94, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_293, c_447])).
% 3.41/1.59  tff(c_484, plain, (![A_96]: (A_96='#skF_2' | k1_xboole_0=A_96 | ~r1_tarski(A_96, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_293, c_458])).
% 3.41/1.59  tff(c_496, plain, (![B_8]: (k3_xboole_0('#skF_2', B_8)='#skF_2' | k3_xboole_0('#skF_2', B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_484])).
% 3.41/1.59  tff(c_961, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_865, c_496])).
% 3.41/1.59  tff(c_970, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_865, c_961])).
% 3.41/1.59  tff(c_972, plain, $false, inference(negUnitSimplification, [status(thm)], [c_292, c_320, c_970])).
% 3.41/1.59  tff(c_973, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_50])).
% 3.41/1.59  tff(c_974, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_50])).
% 3.41/1.59  tff(c_975, plain, (![A_9]: (k5_xboole_0(A_9, '#skF_2')=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_974, c_10])).
% 3.41/1.59  tff(c_12, plain, (r1_xboole_0(k1_xboole_0, k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.41/1.59  tff(c_978, plain, (r1_xboole_0('#skF_2', '#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_974, c_974, c_12])).
% 3.41/1.59  tff(c_16, plain, (![A_11, B_12, C_13]: (k1_xboole_0=A_11 | ~r1_xboole_0(B_12, C_13) | ~r1_tarski(A_11, C_13) | ~r1_tarski(A_11, B_12))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.41/1.59  tff(c_1884, plain, (![A_153, B_154, C_155]: (A_153='#skF_2' | ~r1_xboole_0(B_154, C_155) | ~r1_tarski(A_153, C_155) | ~r1_tarski(A_153, B_154))), inference(demodulation, [status(thm), theory('equality')], [c_974, c_16])).
% 3.41/1.59  tff(c_1888, plain, (![A_156]: (A_156='#skF_2' | ~r1_tarski(A_156, '#skF_2'))), inference(resolution, [status(thm)], [c_978, c_1884])).
% 3.41/1.59  tff(c_1897, plain, (![B_8]: (k3_xboole_0('#skF_2', B_8)='#skF_2')), inference(resolution, [status(thm)], [c_8, c_1888])).
% 3.41/1.59  tff(c_1189, plain, (![A_134, B_135]: (k5_xboole_0(k5_xboole_0(A_134, B_135), k2_xboole_0(A_134, B_135))=k3_xboole_0(A_134, B_135))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.41/1.59  tff(c_1231, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_3'), k1_tarski('#skF_1'))=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_54, c_1189])).
% 3.41/1.59  tff(c_1238, plain, (k5_xboole_0('#skF_3', k1_tarski('#skF_1'))=k3_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_975, c_2, c_1231])).
% 3.41/1.59  tff(c_1034, plain, (![B_121, A_122]: (k5_xboole_0(B_121, A_122)=k5_xboole_0(A_122, B_121))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.41/1.59  tff(c_1050, plain, (![A_122]: (k5_xboole_0('#skF_2', A_122)=A_122)), inference(superposition, [status(thm), theory('equality')], [c_1034, c_975])).
% 3.41/1.59  tff(c_976, plain, (![A_19]: (k5_xboole_0(A_19, A_19)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_974, c_22])).
% 3.41/1.59  tff(c_1315, plain, (![A_138, B_139, C_140]: (k5_xboole_0(k5_xboole_0(A_138, B_139), C_140)=k5_xboole_0(A_138, k5_xboole_0(B_139, C_140)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.41/1.59  tff(c_1406, plain, (![A_19, C_140]: (k5_xboole_0(A_19, k5_xboole_0(A_19, C_140))=k5_xboole_0('#skF_2', C_140))), inference(superposition, [status(thm), theory('equality')], [c_976, c_1315])).
% 3.41/1.59  tff(c_1420, plain, (![A_141, C_142]: (k5_xboole_0(A_141, k5_xboole_0(A_141, C_142))=C_142)), inference(demodulation, [status(thm), theory('equality')], [c_1050, c_1406])).
% 3.41/1.59  tff(c_1462, plain, (k5_xboole_0('#skF_3', k3_xboole_0('#skF_2', '#skF_3'))=k1_tarski('#skF_1')), inference(superposition, [status(thm), theory('equality')], [c_1238, c_1420])).
% 3.41/1.59  tff(c_1901, plain, (k5_xboole_0('#skF_3', '#skF_2')=k1_tarski('#skF_1')), inference(demodulation, [status(thm), theory('equality')], [c_1897, c_1462])).
% 3.41/1.59  tff(c_1904, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_975, c_1901])).
% 3.41/1.59  tff(c_1906, plain, $false, inference(negUnitSimplification, [status(thm)], [c_973, c_1904])).
% 3.41/1.59  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 3.41/1.59  
% 3.41/1.59  Inference rules
% 3.41/1.59  ----------------------
% 3.41/1.59  #Ref     : 0
% 3.41/1.59  #Sup     : 455
% 3.41/1.59  #Fact    : 1
% 3.41/1.59  #Define  : 0
% 3.41/1.59  #Split   : 3
% 3.41/1.59  #Chain   : 0
% 3.41/1.59  #Close   : 0
% 3.41/1.59  
% 3.41/1.59  Ordering : KBO
% 3.41/1.59  
% 3.41/1.59  Simplification rules
% 3.41/1.59  ----------------------
% 3.41/1.59  #Subsume      : 8
% 3.41/1.59  #Demod        : 203
% 3.41/1.59  #Tautology    : 290
% 3.41/1.59  #SimpNegUnit  : 7
% 3.41/1.59  #BackRed      : 11
% 3.41/1.59  
% 3.41/1.59  #Partial instantiations: 0
% 3.41/1.59  #Strategies tried      : 1
% 3.41/1.59  
% 3.41/1.59  Timing (in seconds)
% 3.41/1.59  ----------------------
% 3.41/1.59  Preprocessing        : 0.33
% 3.41/1.59  Parsing              : 0.18
% 3.41/1.59  CNF conversion       : 0.02
% 3.41/1.59  Main loop            : 0.44
% 3.41/1.59  Inferencing          : 0.15
% 3.41/1.59  Reduction            : 0.17
% 3.41/1.59  Demodulation         : 0.14
% 3.41/1.59  BG Simplification    : 0.02
% 3.41/1.59  Subsumption          : 0.06
% 3.41/1.59  Abstraction          : 0.02
% 3.41/1.59  MUC search           : 0.00
% 3.41/1.59  Cooper               : 0.00
% 3.41/1.59  Total                : 0.80
% 3.41/1.59  Index Insertion      : 0.00
% 3.41/1.59  Index Deletion       : 0.00
% 3.41/1.59  Index Matching       : 0.00
% 3.41/1.59  BG Taut test         : 0.00
%------------------------------------------------------------------------------

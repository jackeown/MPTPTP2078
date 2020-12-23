%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n015.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:23 EST 2020

% Result     : Theorem 3.10s
% Output     : CNFRefutation 3.10s
% Verified   : 
% Statistics : Number of formulae       :   76 ( 156 expanded)
%              Number of leaves         :   29 (  63 expanded)
%              Depth                    :   11
%              Number of atoms          :   82 ( 263 expanded)
%              Number of equality atoms :   64 ( 244 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#nlpp',type,(
    '#nlpp': ( $real * $real ) > $real )).

tff(k1_tarski,type,(
    k1_tarski: $i > $i )).

tff(k1_xboole_0,type,(
    k1_xboole_0: $i )).

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

tff(f_82,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( k1_tarski(A) = k2_xboole_0(B,C)
          & ~ ( B = k1_tarski(A)
              & C = k1_tarski(A) )
          & ~ ( B = k1_xboole_0
              & C = k1_tarski(A) )
          & ~ ( B = k1_tarski(A)
              & C = k1_xboole_0 ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t43_zfmisc_1)).

tff(f_37,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_33,axiom,(
    ! [A] : r1_tarski(k1_xboole_0,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k2_xboole_0(A,B) = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t12_xboole_1)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_40,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_91,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_40])).

tff(c_38,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_77,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_38])).

tff(c_44,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_87,plain,(
    ! [A_46,B_47] : r1_tarski(A_46,k2_xboole_0(A_46,B_47)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_90,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_87])).

tff(c_232,plain,(
    ! [B_64,A_65] :
      ( k1_tarski(B_64) = A_65
      | k1_xboole_0 = A_65
      | ~ r1_tarski(A_65,k1_tarski(B_64)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_242,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_90,c_232])).

tff(c_253,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_91,c_77,c_242])).

tff(c_254,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_255,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_40])).

tff(c_6,plain,(
    ! [A_5] : r1_tarski(k1_xboole_0,A_5) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_258,plain,(
    ! [A_5] : r1_tarski('#skF_2',A_5) ),
    inference(demodulation,[status(thm),theory(equality)],[c_255,c_6])).

tff(c_339,plain,(
    ! [A_78,B_79] :
      ( k2_xboole_0(A_78,B_79) = B_79
      | ~ r1_tarski(A_78,B_79) ) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_358,plain,(
    ! [A_5] : k2_xboole_0('#skF_2',A_5) = A_5 ),
    inference(resolution,[status(thm)],[c_258,c_339])).

tff(c_378,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_358,c_44])).

tff(c_380,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_254,c_378])).

tff(c_381,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_382,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_38])).

tff(c_42,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_400,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_382,c_42])).

tff(c_8,plain,(
    ! [A_6] : k5_xboole_0(A_6,k1_xboole_0) = A_6 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_891,plain,(
    ! [A_113,B_114,C_115] : k5_xboole_0(k5_xboole_0(A_113,B_114),C_115) = k5_xboole_0(A_113,k5_xboole_0(B_114,C_115)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_14,plain,(
    ! [A_12] : k5_xboole_0(A_12,A_12) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_905,plain,(
    ! [A_113,B_114] : k5_xboole_0(A_113,k5_xboole_0(B_114,k5_xboole_0(A_113,B_114))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_891,c_14])).

tff(c_1315,plain,(
    ! [A_126,C_127] : k5_xboole_0(A_126,k5_xboole_0(A_126,C_127)) = k5_xboole_0(k1_xboole_0,C_127) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_891])).

tff(c_1401,plain,(
    ! [A_12] : k5_xboole_0(k1_xboole_0,A_12) = k5_xboole_0(A_12,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_1315])).

tff(c_1422,plain,(
    ! [A_12] : k5_xboole_0(k1_xboole_0,A_12) = A_12 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1401])).

tff(c_921,plain,(
    ! [A_12,C_115] : k5_xboole_0(A_12,k5_xboole_0(A_12,C_115)) = k5_xboole_0(k1_xboole_0,C_115) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_891])).

tff(c_1561,plain,(
    ! [A_136,C_137] : k5_xboole_0(A_136,k5_xboole_0(A_136,C_137)) = C_137 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1422,c_921])).

tff(c_1617,plain,(
    ! [B_114,A_113] : k5_xboole_0(B_114,k5_xboole_0(A_113,B_114)) = k5_xboole_0(A_113,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_905,c_1561])).

tff(c_1647,plain,(
    ! [B_114,A_113] : k5_xboole_0(B_114,k5_xboole_0(A_113,B_114)) = A_113 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_1617])).

tff(c_383,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_44])).

tff(c_1028,plain,(
    ! [A_119,B_120] : k5_xboole_0(k5_xboole_0(A_119,B_120),k2_xboole_0(A_119,B_120)) = k3_xboole_0(A_119,B_120) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_1098,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_3'),'#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_383,c_1028])).

tff(c_12,plain,(
    ! [A_9,B_10,C_11] : k5_xboole_0(k5_xboole_0(A_9,B_10),C_11) = k5_xboole_0(A_9,k5_xboole_0(B_10,C_11)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1296,plain,(
    k5_xboole_0('#skF_2',k5_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_1098,c_12])).

tff(c_1787,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1647,c_1296])).

tff(c_4,plain,(
    ! [A_3,B_4] : r1_tarski(k3_xboole_0(A_3,B_4),A_3) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_594,plain,(
    ! [B_101,A_102] :
      ( k1_tarski(B_101) = A_102
      | k1_xboole_0 = A_102
      | ~ r1_tarski(A_102,k1_tarski(B_101)) ) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_604,plain,(
    ! [A_102] :
      ( k1_tarski('#skF_1') = A_102
      | k1_xboole_0 = A_102
      | ~ r1_tarski(A_102,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_382,c_594])).

tff(c_632,plain,(
    ! [A_103] :
      ( A_103 = '#skF_2'
      | k1_xboole_0 = A_103
      | ~ r1_tarski(A_103,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_382,c_604])).

tff(c_644,plain,(
    ! [B_4] :
      ( k3_xboole_0('#skF_2',B_4) = '#skF_2'
      | k3_xboole_0('#skF_2',B_4) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_4,c_632])).

tff(c_1871,plain,
    ( k3_xboole_0('#skF_2','#skF_3') = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1787,c_644])).

tff(c_1883,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1787,c_1871])).

tff(c_1885,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_381,c_400,c_1883])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n015.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:24:08 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.10/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.49  
% 3.10/1.49  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.49  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.10/1.49  
% 3.10/1.49  %Foreground sorts:
% 3.10/1.49  
% 3.10/1.49  
% 3.10/1.49  %Background operators:
% 3.10/1.49  
% 3.10/1.49  
% 3.10/1.49  %Foreground operators:
% 3.10/1.49  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.10/1.49  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.10/1.49  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.10/1.49  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.10/1.49  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.10/1.49  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.10/1.49  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.10/1.49  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.10/1.49  tff('#skF_2', type, '#skF_2': $i).
% 3.10/1.49  tff('#skF_3', type, '#skF_3': $i).
% 3.10/1.49  tff('#skF_1', type, '#skF_1': $i).
% 3.10/1.49  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.10/1.49  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.10/1.49  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.10/1.49  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.10/1.49  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.10/1.49  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.10/1.49  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.10/1.49  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.10/1.49  
% 3.10/1.51  tff(f_82, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.10/1.51  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.10/1.51  tff(f_61, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.10/1.51  tff(f_33, axiom, (![A]: r1_tarski(k1_xboole_0, A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_xboole_1)).
% 3.10/1.51  tff(f_29, axiom, (![A, B]: (r1_tarski(A, B) => (k2_xboole_0(A, B) = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t12_xboole_1)).
% 3.10/1.51  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.10/1.51  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.10/1.51  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.10/1.51  tff(f_43, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.10/1.51  tff(f_31, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.10/1.51  tff(c_40, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.10/1.51  tff(c_91, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_40])).
% 3.10/1.51  tff(c_38, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.10/1.51  tff(c_77, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_38])).
% 3.10/1.51  tff(c_44, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.10/1.51  tff(c_87, plain, (![A_46, B_47]: (r1_tarski(A_46, k2_xboole_0(A_46, B_47)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.10/1.51  tff(c_90, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_44, c_87])).
% 3.10/1.51  tff(c_232, plain, (![B_64, A_65]: (k1_tarski(B_64)=A_65 | k1_xboole_0=A_65 | ~r1_tarski(A_65, k1_tarski(B_64)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.10/1.51  tff(c_242, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_90, c_232])).
% 3.10/1.51  tff(c_253, plain, $false, inference(negUnitSimplification, [status(thm)], [c_91, c_77, c_242])).
% 3.10/1.51  tff(c_254, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_40])).
% 3.10/1.51  tff(c_255, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_40])).
% 3.10/1.51  tff(c_6, plain, (![A_5]: (r1_tarski(k1_xboole_0, A_5))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.10/1.51  tff(c_258, plain, (![A_5]: (r1_tarski('#skF_2', A_5))), inference(demodulation, [status(thm), theory('equality')], [c_255, c_6])).
% 3.10/1.51  tff(c_339, plain, (![A_78, B_79]: (k2_xboole_0(A_78, B_79)=B_79 | ~r1_tarski(A_78, B_79))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.10/1.51  tff(c_358, plain, (![A_5]: (k2_xboole_0('#skF_2', A_5)=A_5)), inference(resolution, [status(thm)], [c_258, c_339])).
% 3.10/1.51  tff(c_378, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_358, c_44])).
% 3.10/1.51  tff(c_380, plain, $false, inference(negUnitSimplification, [status(thm)], [c_254, c_378])).
% 3.10/1.51  tff(c_381, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_38])).
% 3.10/1.51  tff(c_382, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_38])).
% 3.10/1.51  tff(c_42, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.10/1.51  tff(c_400, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_382, c_382, c_42])).
% 3.10/1.51  tff(c_8, plain, (![A_6]: (k5_xboole_0(A_6, k1_xboole_0)=A_6)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.10/1.51  tff(c_891, plain, (![A_113, B_114, C_115]: (k5_xboole_0(k5_xboole_0(A_113, B_114), C_115)=k5_xboole_0(A_113, k5_xboole_0(B_114, C_115)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.10/1.51  tff(c_14, plain, (![A_12]: (k5_xboole_0(A_12, A_12)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.10/1.51  tff(c_905, plain, (![A_113, B_114]: (k5_xboole_0(A_113, k5_xboole_0(B_114, k5_xboole_0(A_113, B_114)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_891, c_14])).
% 3.10/1.51  tff(c_1315, plain, (![A_126, C_127]: (k5_xboole_0(A_126, k5_xboole_0(A_126, C_127))=k5_xboole_0(k1_xboole_0, C_127))), inference(superposition, [status(thm), theory('equality')], [c_14, c_891])).
% 3.10/1.51  tff(c_1401, plain, (![A_12]: (k5_xboole_0(k1_xboole_0, A_12)=k5_xboole_0(A_12, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_1315])).
% 3.10/1.51  tff(c_1422, plain, (![A_12]: (k5_xboole_0(k1_xboole_0, A_12)=A_12)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1401])).
% 3.10/1.51  tff(c_921, plain, (![A_12, C_115]: (k5_xboole_0(A_12, k5_xboole_0(A_12, C_115))=k5_xboole_0(k1_xboole_0, C_115))), inference(superposition, [status(thm), theory('equality')], [c_14, c_891])).
% 3.10/1.51  tff(c_1561, plain, (![A_136, C_137]: (k5_xboole_0(A_136, k5_xboole_0(A_136, C_137))=C_137)), inference(demodulation, [status(thm), theory('equality')], [c_1422, c_921])).
% 3.10/1.51  tff(c_1617, plain, (![B_114, A_113]: (k5_xboole_0(B_114, k5_xboole_0(A_113, B_114))=k5_xboole_0(A_113, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_905, c_1561])).
% 3.10/1.51  tff(c_1647, plain, (![B_114, A_113]: (k5_xboole_0(B_114, k5_xboole_0(A_113, B_114))=A_113)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_1617])).
% 3.10/1.51  tff(c_383, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_382, c_44])).
% 3.10/1.51  tff(c_1028, plain, (![A_119, B_120]: (k5_xboole_0(k5_xboole_0(A_119, B_120), k2_xboole_0(A_119, B_120))=k3_xboole_0(A_119, B_120))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.10/1.51  tff(c_1098, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_3'), '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_383, c_1028])).
% 3.10/1.51  tff(c_12, plain, (![A_9, B_10, C_11]: (k5_xboole_0(k5_xboole_0(A_9, B_10), C_11)=k5_xboole_0(A_9, k5_xboole_0(B_10, C_11)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.10/1.51  tff(c_1296, plain, (k5_xboole_0('#skF_2', k5_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_1098, c_12])).
% 3.10/1.51  tff(c_1787, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1647, c_1296])).
% 3.10/1.51  tff(c_4, plain, (![A_3, B_4]: (r1_tarski(k3_xboole_0(A_3, B_4), A_3))), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.10/1.51  tff(c_594, plain, (![B_101, A_102]: (k1_tarski(B_101)=A_102 | k1_xboole_0=A_102 | ~r1_tarski(A_102, k1_tarski(B_101)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.10/1.51  tff(c_604, plain, (![A_102]: (k1_tarski('#skF_1')=A_102 | k1_xboole_0=A_102 | ~r1_tarski(A_102, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_382, c_594])).
% 3.10/1.51  tff(c_632, plain, (![A_103]: (A_103='#skF_2' | k1_xboole_0=A_103 | ~r1_tarski(A_103, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_382, c_604])).
% 3.10/1.51  tff(c_644, plain, (![B_4]: (k3_xboole_0('#skF_2', B_4)='#skF_2' | k3_xboole_0('#skF_2', B_4)=k1_xboole_0)), inference(resolution, [status(thm)], [c_4, c_632])).
% 3.10/1.51  tff(c_1871, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1787, c_644])).
% 3.10/1.51  tff(c_1883, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1787, c_1871])).
% 3.10/1.51  tff(c_1885, plain, $false, inference(negUnitSimplification, [status(thm)], [c_381, c_400, c_1883])).
% 3.10/1.51  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.10/1.51  
% 3.10/1.51  Inference rules
% 3.10/1.51  ----------------------
% 3.10/1.51  #Ref     : 0
% 3.10/1.51  #Sup     : 457
% 3.10/1.51  #Fact    : 1
% 3.10/1.51  #Define  : 0
% 3.10/1.51  #Split   : 3
% 3.10/1.51  #Chain   : 0
% 3.10/1.51  #Close   : 0
% 3.10/1.51  
% 3.10/1.51  Ordering : KBO
% 3.10/1.51  
% 3.10/1.51  Simplification rules
% 3.10/1.51  ----------------------
% 3.10/1.51  #Subsume      : 7
% 3.10/1.51  #Demod        : 282
% 3.10/1.51  #Tautology    : 310
% 3.10/1.51  #SimpNegUnit  : 12
% 3.10/1.51  #BackRed      : 15
% 3.10/1.51  
% 3.10/1.51  #Partial instantiations: 0
% 3.10/1.51  #Strategies tried      : 1
% 3.10/1.51  
% 3.10/1.51  Timing (in seconds)
% 3.10/1.51  ----------------------
% 3.10/1.51  Preprocessing        : 0.31
% 3.10/1.51  Parsing              : 0.17
% 3.10/1.51  CNF conversion       : 0.02
% 3.10/1.51  Main loop            : 0.44
% 3.10/1.51  Inferencing          : 0.16
% 3.10/1.51  Reduction            : 0.16
% 3.10/1.51  Demodulation         : 0.13
% 3.10/1.51  BG Simplification    : 0.02
% 3.10/1.51  Subsumption          : 0.06
% 3.10/1.51  Abstraction          : 0.02
% 3.10/1.51  MUC search           : 0.00
% 3.10/1.51  Cooper               : 0.00
% 3.10/1.51  Total                : 0.78
% 3.10/1.51  Index Insertion      : 0.00
% 3.10/1.51  Index Deletion       : 0.00
% 3.10/1.51  Index Matching       : 0.00
% 3.10/1.51  BG Taut test         : 0.00
%------------------------------------------------------------------------------

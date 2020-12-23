%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n014.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:16 EST 2020

% Result     : Theorem 3.15s
% Output     : CNFRefutation 3.15s
% Verified   : 
% Statistics : Number of formulae       :   78 ( 142 expanded)
%              Number of leaves         :   32 (  60 expanded)
%              Depth                    :    9
%              Number of atoms          :   81 ( 246 expanded)
%              Number of equality atoms :   68 ( 232 expanded)
%              Maximal formula depth    :   11 (   3 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1

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

tff(f_86,negated_conjecture,(
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

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_tarski(A,k1_tarski(B))
    <=> ( A = k1_xboole_0
        | A = k1_tarski(B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l3_zfmisc_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_41,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(k5_xboole_0(A,B),k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t93_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_35,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_39,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(c_46,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_xboole_0 != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_110,plain,(
    k1_xboole_0 != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_46])).

tff(c_44,plain,
    ( k1_xboole_0 != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_96,plain,(
    k1_tarski('#skF_1') != '#skF_2' ),
    inference(splitLeft,[status(thm)],[c_44])).

tff(c_50,plain,(
    k2_xboole_0('#skF_2','#skF_3') = k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_112,plain,(
    ! [A_59,B_60] : r1_tarski(A_59,k2_xboole_0(A_59,B_60)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_115,plain,(
    r1_tarski('#skF_2',k1_tarski('#skF_1')) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_112])).

tff(c_263,plain,(
    ! [B_75,A_76] :
      ( k1_tarski(B_75) = A_76
      | k1_xboole_0 = A_76
      | ~ r1_tarski(A_76,k1_tarski(B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_270,plain,
    ( k1_tarski('#skF_1') = '#skF_2'
    | k1_xboole_0 = '#skF_2' ),
    inference(resolution,[status(thm)],[c_115,c_263])).

tff(c_282,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_110,c_96,c_270])).

tff(c_283,plain,(
    k1_tarski('#skF_1') != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_284,plain,(
    k1_xboole_0 = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_46])).

tff(c_16,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_286,plain,(
    ! [A_15] : k5_xboole_0(A_15,A_15) = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_284,c_16])).

tff(c_490,plain,(
    ! [A_99,B_100] : k2_xboole_0(k5_xboole_0(A_99,B_100),k3_xboole_0(A_99,B_100)) = k2_xboole_0(A_99,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_511,plain,(
    ! [A_15] : k2_xboole_0('#skF_2',k3_xboole_0(A_15,A_15)) = k2_xboole_0(A_15,A_15) ),
    inference(superposition,[status(thm),theory(equality)],[c_286,c_490])).

tff(c_520,plain,(
    ! [A_15] : k2_xboole_0('#skF_2',A_15) = A_15 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_4,c_511])).

tff(c_580,plain,(
    k1_tarski('#skF_1') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_520,c_50])).

tff(c_582,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_283,c_580])).

tff(c_583,plain,(
    k1_xboole_0 != '#skF_3' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_584,plain,(
    k1_tarski('#skF_1') = '#skF_2' ),
    inference(splitRight,[status(thm)],[c_44])).

tff(c_48,plain,
    ( k1_tarski('#skF_1') != '#skF_3'
    | k1_tarski('#skF_1') != '#skF_2' ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_634,plain,(
    '#skF_2' != '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_584,c_48])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_635,plain,(
    ! [B_110,A_111] : k5_xboole_0(B_110,A_111) = k5_xboole_0(A_111,B_110) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_651,plain,(
    ! [A_111] : k5_xboole_0(k1_xboole_0,A_111) = A_111 ),
    inference(superposition,[status(thm),theory(equality)],[c_635,c_10])).

tff(c_972,plain,(
    ! [A_129,B_130,C_131] : k5_xboole_0(k5_xboole_0(A_129,B_130),C_131) = k5_xboole_0(A_129,k5_xboole_0(B_130,C_131)) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_1063,plain,(
    ! [A_15,C_131] : k5_xboole_0(A_15,k5_xboole_0(A_15,C_131)) = k5_xboole_0(k1_xboole_0,C_131) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_972])).

tff(c_1078,plain,(
    ! [A_132,C_133] : k5_xboole_0(A_132,k5_xboole_0(A_132,C_133)) = C_133 ),
    inference(demodulation,[status(thm),theory(equality)],[c_651,c_1063])).

tff(c_1133,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_1078])).

tff(c_603,plain,(
    k2_xboole_0('#skF_2','#skF_3') = '#skF_2' ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_50])).

tff(c_850,plain,(
    ! [A_125,B_126] : k5_xboole_0(k5_xboole_0(A_125,B_126),k2_xboole_0(A_125,B_126)) = k3_xboole_0(A_125,B_126) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_886,plain,(
    k5_xboole_0(k5_xboole_0('#skF_2','#skF_3'),'#skF_2') = k3_xboole_0('#skF_2','#skF_3') ),
    inference(superposition,[status(thm),theory(equality)],[c_603,c_850])).

tff(c_898,plain,(
    k5_xboole_0('#skF_2',k5_xboole_0('#skF_3','#skF_2')) = k3_xboole_0('#skF_2','#skF_3') ),
    inference(demodulation,[status(thm),theory(equality)],[c_2,c_2,c_886])).

tff(c_1155,plain,(
    k3_xboole_0('#skF_2','#skF_3') = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1133,c_898])).

tff(c_8,plain,(
    ! [A_7,B_8] : r1_tarski(k3_xboole_0(A_7,B_8),A_7) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_779,plain,(
    ! [B_121,A_122] :
      ( k1_tarski(B_121) = A_122
      | k1_xboole_0 = A_122
      | ~ r1_tarski(A_122,k1_tarski(B_121)) ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_790,plain,(
    ! [A_122] :
      ( k1_tarski('#skF_1') = A_122
      | k1_xboole_0 = A_122
      | ~ r1_tarski(A_122,'#skF_2') ) ),
    inference(superposition,[status(thm),theory(equality)],[c_584,c_779])).

tff(c_800,plain,(
    ! [A_123] :
      ( A_123 = '#skF_2'
      | k1_xboole_0 = A_123
      | ~ r1_tarski(A_123,'#skF_2') ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_584,c_790])).

tff(c_816,plain,(
    ! [B_8] :
      ( k3_xboole_0('#skF_2',B_8) = '#skF_2'
      | k3_xboole_0('#skF_2',B_8) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_800])).

tff(c_1358,plain,
    ( k3_xboole_0('#skF_2','#skF_3') = '#skF_2'
    | k1_xboole_0 = '#skF_3' ),
    inference(superposition,[status(thm),theory(equality)],[c_1155,c_816])).

tff(c_1368,plain,
    ( '#skF_2' = '#skF_3'
    | k1_xboole_0 = '#skF_3' ),
    inference(demodulation,[status(thm),theory(equality)],[c_1155,c_1358])).

tff(c_1370,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_583,c_634,c_1368])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n014.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 12:53:22 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.15/1.49  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.50  
% 3.15/1.50  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.50  %$ r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_1
% 3.15/1.50  
% 3.15/1.50  %Foreground sorts:
% 3.15/1.50  
% 3.15/1.50  
% 3.15/1.50  %Background operators:
% 3.15/1.50  
% 3.15/1.50  
% 3.15/1.50  %Foreground operators:
% 3.15/1.50  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.15/1.50  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.15/1.50  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.15/1.50  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.15/1.50  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.15/1.50  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.15/1.50  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.15/1.50  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.15/1.50  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.15/1.50  tff('#skF_2', type, '#skF_2': $i).
% 3.15/1.50  tff('#skF_3', type, '#skF_3': $i).
% 3.15/1.50  tff('#skF_1', type, '#skF_1': $i).
% 3.15/1.50  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.50  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.50  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.15/1.50  tff(k3_tarski, type, k3_tarski: $i > $i).
% 3.15/1.50  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.15/1.50  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.15/1.50  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.15/1.50  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.15/1.50  
% 3.15/1.52  tff(f_86, negated_conjecture, ~(![A, B, C]: ~((((k1_tarski(A) = k2_xboole_0(B, C)) & ~((B = k1_tarski(A)) & (C = k1_tarski(A)))) & ~((B = k1_xboole_0) & (C = k1_tarski(A)))) & ~((B = k1_tarski(A)) & (C = k1_xboole_0)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t43_zfmisc_1)).
% 3.15/1.52  tff(f_37, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_1)).
% 3.15/1.52  tff(f_65, axiom, (![A, B]: (r1_tarski(A, k1_tarski(B)) <=> ((A = k1_xboole_0) | (A = k1_tarski(B))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l3_zfmisc_1)).
% 3.15/1.52  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.15/1.52  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 3.15/1.52  tff(f_41, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 3.15/1.52  tff(f_43, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(k5_xboole_0(A, B), k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t93_xboole_1)).
% 3.15/1.52  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 3.15/1.52  tff(f_35, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.15/1.52  tff(f_39, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 3.15/1.52  tff(f_45, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 3.15/1.52  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 3.15/1.52  tff(c_46, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_xboole_0!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.15/1.52  tff(c_110, plain, (k1_xboole_0!='#skF_2'), inference(splitLeft, [status(thm)], [c_46])).
% 3.15/1.52  tff(c_44, plain, (k1_xboole_0!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.15/1.52  tff(c_96, plain, (k1_tarski('#skF_1')!='#skF_2'), inference(splitLeft, [status(thm)], [c_44])).
% 3.15/1.52  tff(c_50, plain, (k2_xboole_0('#skF_2', '#skF_3')=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.15/1.52  tff(c_112, plain, (![A_59, B_60]: (r1_tarski(A_59, k2_xboole_0(A_59, B_60)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.15/1.52  tff(c_115, plain, (r1_tarski('#skF_2', k1_tarski('#skF_1'))), inference(superposition, [status(thm), theory('equality')], [c_50, c_112])).
% 3.15/1.52  tff(c_263, plain, (![B_75, A_76]: (k1_tarski(B_75)=A_76 | k1_xboole_0=A_76 | ~r1_tarski(A_76, k1_tarski(B_75)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.52  tff(c_270, plain, (k1_tarski('#skF_1')='#skF_2' | k1_xboole_0='#skF_2'), inference(resolution, [status(thm)], [c_115, c_263])).
% 3.15/1.52  tff(c_282, plain, $false, inference(negUnitSimplification, [status(thm)], [c_110, c_96, c_270])).
% 3.15/1.52  tff(c_283, plain, (k1_tarski('#skF_1')!='#skF_3'), inference(splitRight, [status(thm)], [c_46])).
% 3.15/1.52  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.15/1.52  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.15/1.52  tff(c_284, plain, (k1_xboole_0='#skF_2'), inference(splitRight, [status(thm)], [c_46])).
% 3.15/1.52  tff(c_16, plain, (![A_15]: (k5_xboole_0(A_15, A_15)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.15/1.52  tff(c_286, plain, (![A_15]: (k5_xboole_0(A_15, A_15)='#skF_2')), inference(demodulation, [status(thm), theory('equality')], [c_284, c_16])).
% 3.15/1.52  tff(c_490, plain, (![A_99, B_100]: (k2_xboole_0(k5_xboole_0(A_99, B_100), k3_xboole_0(A_99, B_100))=k2_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.15/1.52  tff(c_511, plain, (![A_15]: (k2_xboole_0('#skF_2', k3_xboole_0(A_15, A_15))=k2_xboole_0(A_15, A_15))), inference(superposition, [status(thm), theory('equality')], [c_286, c_490])).
% 3.15/1.52  tff(c_520, plain, (![A_15]: (k2_xboole_0('#skF_2', A_15)=A_15)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_4, c_511])).
% 3.15/1.52  tff(c_580, plain, (k1_tarski('#skF_1')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_520, c_50])).
% 3.15/1.52  tff(c_582, plain, $false, inference(negUnitSimplification, [status(thm)], [c_283, c_580])).
% 3.15/1.52  tff(c_583, plain, (k1_xboole_0!='#skF_3'), inference(splitRight, [status(thm)], [c_44])).
% 3.15/1.52  tff(c_584, plain, (k1_tarski('#skF_1')='#skF_2'), inference(splitRight, [status(thm)], [c_44])).
% 3.15/1.52  tff(c_48, plain, (k1_tarski('#skF_1')!='#skF_3' | k1_tarski('#skF_1')!='#skF_2'), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.15/1.52  tff(c_634, plain, ('#skF_2'!='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_584, c_584, c_48])).
% 3.15/1.52  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.52  tff(c_635, plain, (![B_110, A_111]: (k5_xboole_0(B_110, A_111)=k5_xboole_0(A_111, B_110))), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.15/1.52  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_35])).
% 3.15/1.52  tff(c_651, plain, (![A_111]: (k5_xboole_0(k1_xboole_0, A_111)=A_111)), inference(superposition, [status(thm), theory('equality')], [c_635, c_10])).
% 3.15/1.52  tff(c_972, plain, (![A_129, B_130, C_131]: (k5_xboole_0(k5_xboole_0(A_129, B_130), C_131)=k5_xboole_0(A_129, k5_xboole_0(B_130, C_131)))), inference(cnfTransformation, [status(thm)], [f_39])).
% 3.15/1.52  tff(c_1063, plain, (![A_15, C_131]: (k5_xboole_0(A_15, k5_xboole_0(A_15, C_131))=k5_xboole_0(k1_xboole_0, C_131))), inference(superposition, [status(thm), theory('equality')], [c_16, c_972])).
% 3.15/1.52  tff(c_1078, plain, (![A_132, C_133]: (k5_xboole_0(A_132, k5_xboole_0(A_132, C_133))=C_133)), inference(demodulation, [status(thm), theory('equality')], [c_651, c_1063])).
% 3.15/1.52  tff(c_1133, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_1078])).
% 3.15/1.52  tff(c_603, plain, (k2_xboole_0('#skF_2', '#skF_3')='#skF_2'), inference(demodulation, [status(thm), theory('equality')], [c_584, c_50])).
% 3.15/1.52  tff(c_850, plain, (![A_125, B_126]: (k5_xboole_0(k5_xboole_0(A_125, B_126), k2_xboole_0(A_125, B_126))=k3_xboole_0(A_125, B_126))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.15/1.52  tff(c_886, plain, (k5_xboole_0(k5_xboole_0('#skF_2', '#skF_3'), '#skF_2')=k3_xboole_0('#skF_2', '#skF_3')), inference(superposition, [status(thm), theory('equality')], [c_603, c_850])).
% 3.15/1.52  tff(c_898, plain, (k5_xboole_0('#skF_2', k5_xboole_0('#skF_3', '#skF_2'))=k3_xboole_0('#skF_2', '#skF_3')), inference(demodulation, [status(thm), theory('equality')], [c_2, c_2, c_886])).
% 3.15/1.52  tff(c_1155, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1133, c_898])).
% 3.15/1.52  tff(c_8, plain, (![A_7, B_8]: (r1_tarski(k3_xboole_0(A_7, B_8), A_7))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.15/1.52  tff(c_779, plain, (![B_121, A_122]: (k1_tarski(B_121)=A_122 | k1_xboole_0=A_122 | ~r1_tarski(A_122, k1_tarski(B_121)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.15/1.52  tff(c_790, plain, (![A_122]: (k1_tarski('#skF_1')=A_122 | k1_xboole_0=A_122 | ~r1_tarski(A_122, '#skF_2'))), inference(superposition, [status(thm), theory('equality')], [c_584, c_779])).
% 3.15/1.52  tff(c_800, plain, (![A_123]: (A_123='#skF_2' | k1_xboole_0=A_123 | ~r1_tarski(A_123, '#skF_2'))), inference(demodulation, [status(thm), theory('equality')], [c_584, c_790])).
% 3.15/1.52  tff(c_816, plain, (![B_8]: (k3_xboole_0('#skF_2', B_8)='#skF_2' | k3_xboole_0('#skF_2', B_8)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_800])).
% 3.15/1.52  tff(c_1358, plain, (k3_xboole_0('#skF_2', '#skF_3')='#skF_2' | k1_xboole_0='#skF_3'), inference(superposition, [status(thm), theory('equality')], [c_1155, c_816])).
% 3.15/1.52  tff(c_1368, plain, ('#skF_2'='#skF_3' | k1_xboole_0='#skF_3'), inference(demodulation, [status(thm), theory('equality')], [c_1155, c_1358])).
% 3.15/1.52  tff(c_1370, plain, $false, inference(negUnitSimplification, [status(thm)], [c_583, c_634, c_1368])).
% 3.15/1.52  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.15/1.52  
% 3.15/1.52  Inference rules
% 3.15/1.52  ----------------------
% 3.15/1.52  #Ref     : 0
% 3.15/1.52  #Sup     : 316
% 3.15/1.52  #Fact    : 1
% 3.15/1.52  #Define  : 0
% 3.15/1.52  #Split   : 3
% 3.15/1.52  #Chain   : 0
% 3.15/1.52  #Close   : 0
% 3.15/1.52  
% 3.15/1.52  Ordering : KBO
% 3.15/1.52  
% 3.15/1.52  Simplification rules
% 3.15/1.52  ----------------------
% 3.15/1.52  #Subsume      : 4
% 3.15/1.52  #Demod        : 135
% 3.15/1.52  #Tautology    : 204
% 3.15/1.52  #SimpNegUnit  : 8
% 3.15/1.52  #BackRed      : 6
% 3.15/1.52  
% 3.15/1.52  #Partial instantiations: 0
% 3.15/1.52  #Strategies tried      : 1
% 3.15/1.52  
% 3.15/1.52  Timing (in seconds)
% 3.15/1.52  ----------------------
% 3.15/1.52  Preprocessing        : 0.33
% 3.15/1.52  Parsing              : 0.17
% 3.15/1.52  CNF conversion       : 0.02
% 3.15/1.52  Main loop            : 0.42
% 3.15/1.52  Inferencing          : 0.15
% 3.15/1.52  Reduction            : 0.16
% 3.15/1.52  Demodulation         : 0.12
% 3.15/1.52  BG Simplification    : 0.02
% 3.15/1.52  Subsumption          : 0.06
% 3.15/1.52  Abstraction          : 0.02
% 3.15/1.52  MUC search           : 0.00
% 3.15/1.52  Cooper               : 0.00
% 3.15/1.52  Total                : 0.79
% 3.15/1.52  Index Insertion      : 0.00
% 3.15/1.52  Index Deletion       : 0.00
% 3.15/1.52  Index Matching       : 0.00
% 3.15/1.52  BG Taut test         : 0.00
%------------------------------------------------------------------------------

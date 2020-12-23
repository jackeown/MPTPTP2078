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
% DateTime   : Thu Dec  3 09:49:10 EST 2020

% Result     : Theorem 3.38s
% Output     : CNFRefutation 3.38s
% Verified   : 
% Statistics : Number of formulae       :   81 (  94 expanded)
%              Number of leaves         :   42 (  50 expanded)
%              Depth                    :   10
%              Number of atoms          :   80 ( 103 expanded)
%              Number of equality atoms :   59 (  78 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

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

tff(f_108,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_88,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_92,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_84,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_61,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_65,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_49,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_41,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_68,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_66,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_56,plain,(
    ! [A_37,B_38,C_39] : k2_enumset1(A_37,A_37,B_38,C_39) = k1_enumset1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_54,plain,(
    ! [A_35,B_36] : k1_enumset1(A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_58,plain,(
    ! [A_40,B_41,C_42,D_43] : k3_enumset1(A_40,A_40,B_41,C_42,D_43) = k2_enumset1(A_40,B_41,C_42,D_43) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1040,plain,(
    ! [A_163,C_165,D_161,E_164,B_162] : k2_xboole_0(k2_enumset1(A_163,B_162,C_165,D_161),k1_tarski(E_164)) = k3_enumset1(A_163,B_162,C_165,D_161,E_164) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1049,plain,(
    ! [A_37,B_38,C_39,E_164] : k3_enumset1(A_37,A_37,B_38,C_39,E_164) = k2_xboole_0(k1_enumset1(A_37,B_38,C_39),k1_tarski(E_164)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1040])).

tff(c_1687,plain,(
    ! [A_226,B_227,C_228,E_229] : k2_xboole_0(k1_enumset1(A_226,B_227,C_228),k1_tarski(E_229)) = k2_enumset1(A_226,B_227,C_228,E_229) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1049])).

tff(c_1696,plain,(
    ! [A_35,B_36,E_229] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(E_229)) = k2_enumset1(A_35,A_35,B_36,E_229) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1687])).

tff(c_1701,plain,(
    ! [A_234,B_235,E_236] : k2_xboole_0(k2_tarski(A_234,B_235),k1_tarski(E_236)) = k1_enumset1(A_234,B_235,E_236) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1696])).

tff(c_18,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_14,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_22,plain,(
    ! [A_18,B_19] :
      ( r1_xboole_0(A_18,B_19)
      | k4_xboole_0(A_18,B_19) != A_18 ) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_189,plain,(
    ! [A_92,B_93,C_94] :
      ( ~ r1_xboole_0(A_92,B_93)
      | ~ r2_hidden(C_94,k3_xboole_0(A_92,B_93)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_206,plain,(
    ! [A_97,B_98] :
      ( ~ r1_xboole_0(A_97,B_98)
      | k3_xboole_0(A_97,B_98) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_189])).

tff(c_561,plain,(
    ! [A_121,B_122] :
      ( k3_xboole_0(A_121,B_122) = k1_xboole_0
      | k4_xboole_0(A_121,B_122) != A_121 ) ),
    inference(resolution,[status(thm)],[c_22,c_206])).

tff(c_580,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_561])).

tff(c_309,plain,(
    ! [A_105,B_106] : k4_xboole_0(A_105,k4_xboole_0(A_105,B_106)) = k3_xboole_0(A_105,B_106) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_327,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_309])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_155,plain,(
    ! [A_89,B_90] : k5_xboole_0(A_89,k3_xboole_0(A_89,B_90)) = k4_xboole_0(A_89,B_90) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_167,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_155])).

tff(c_332,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k3_xboole_0(A_1,k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_327,c_167])).

tff(c_70,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_108])).

tff(c_111,plain,(
    ! [A_76,B_77] :
      ( k3_xboole_0(A_76,B_77) = A_76
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_115,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_111])).

tff(c_164,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_115,c_155])).

tff(c_409,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k3_xboole_0(k1_tarski('#skF_5'),k1_xboole_0) ),
    inference(demodulation,[status(thm),theory(equality)],[c_332,c_164])).

tff(c_24,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_416,plain,(
    k5_xboole_0(k2_tarski('#skF_6','#skF_7'),k3_xboole_0(k1_tarski('#skF_5'),k1_xboole_0)) = k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_24])).

tff(c_771,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_580,c_416])).

tff(c_1707,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_1701,c_771])).

tff(c_28,plain,(
    ! [E_28,A_22,B_23] : r2_hidden(E_28,k1_enumset1(A_22,B_23,E_28)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1737,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1707,c_28])).

tff(c_840,plain,(
    ! [E_145,C_146,B_147,A_148] :
      ( E_145 = C_146
      | E_145 = B_147
      | E_145 = A_148
      | ~ r2_hidden(E_145,k1_enumset1(A_148,B_147,C_146)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_847,plain,(
    ! [E_145,B_36,A_35] :
      ( E_145 = B_36
      | E_145 = A_35
      | E_145 = A_35
      | ~ r2_hidden(E_145,k2_tarski(A_35,B_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_840])).

tff(c_1746,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_1737,c_847])).

tff(c_1753,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_68,c_66,c_1746])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.12/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.15/0.34  % Computer   : n015.cluster.edu
% 0.15/0.34  % Model      : x86_64 x86_64
% 0.15/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.15/0.34  % Memory     : 8042.1875MB
% 0.15/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.15/0.34  % CPULimit   : 60
% 0.15/0.34  % DateTime   : Tue Dec  1 20:00:53 EST 2020
% 0.15/0.35  % CPUTime    : 
% 0.15/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.38/1.58  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.59  
% 3.38/1.59  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.59  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.38/1.59  
% 3.38/1.59  %Foreground sorts:
% 3.38/1.59  
% 3.38/1.59  
% 3.38/1.59  %Background operators:
% 3.38/1.59  
% 3.38/1.59  
% 3.38/1.59  %Foreground operators:
% 3.38/1.59  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.38/1.59  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.38/1.59  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.38/1.59  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.38/1.59  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.38/1.59  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.38/1.59  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.38/1.59  tff('#skF_7', type, '#skF_7': $i).
% 3.38/1.59  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.38/1.59  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.38/1.59  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.38/1.59  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.38/1.59  tff('#skF_5', type, '#skF_5': $i).
% 3.38/1.59  tff('#skF_6', type, '#skF_6': $i).
% 3.38/1.59  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.38/1.59  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.38/1.59  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.59  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.38/1.59  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.59  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.38/1.59  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.38/1.59  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.38/1.59  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.38/1.59  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.38/1.59  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.38/1.59  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.38/1.59  
% 3.38/1.60  tff(f_108, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.38/1.60  tff(f_90, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.38/1.60  tff(f_88, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.38/1.60  tff(f_92, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.38/1.60  tff(f_84, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 3.38/1.60  tff(f_61, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.38/1.60  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.38/1.60  tff(f_65, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t83_xboole_1)).
% 3.38/1.60  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.38/1.60  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.38/1.60  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.38/1.60  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.38/1.60  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.38/1.60  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.38/1.60  tff(f_67, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.38/1.60  tff(f_82, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.38/1.60  tff(c_68, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.38/1.60  tff(c_66, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.38/1.60  tff(c_56, plain, (![A_37, B_38, C_39]: (k2_enumset1(A_37, A_37, B_38, C_39)=k1_enumset1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.38/1.60  tff(c_54, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.38/1.60  tff(c_58, plain, (![A_40, B_41, C_42, D_43]: (k3_enumset1(A_40, A_40, B_41, C_42, D_43)=k2_enumset1(A_40, B_41, C_42, D_43))), inference(cnfTransformation, [status(thm)], [f_92])).
% 3.38/1.60  tff(c_1040, plain, (![A_163, C_165, D_161, E_164, B_162]: (k2_xboole_0(k2_enumset1(A_163, B_162, C_165, D_161), k1_tarski(E_164))=k3_enumset1(A_163, B_162, C_165, D_161, E_164))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.38/1.60  tff(c_1049, plain, (![A_37, B_38, C_39, E_164]: (k3_enumset1(A_37, A_37, B_38, C_39, E_164)=k2_xboole_0(k1_enumset1(A_37, B_38, C_39), k1_tarski(E_164)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1040])).
% 3.38/1.60  tff(c_1687, plain, (![A_226, B_227, C_228, E_229]: (k2_xboole_0(k1_enumset1(A_226, B_227, C_228), k1_tarski(E_229))=k2_enumset1(A_226, B_227, C_228, E_229))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1049])).
% 3.38/1.60  tff(c_1696, plain, (![A_35, B_36, E_229]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(E_229))=k2_enumset1(A_35, A_35, B_36, E_229))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1687])).
% 3.38/1.60  tff(c_1701, plain, (![A_234, B_235, E_236]: (k2_xboole_0(k2_tarski(A_234, B_235), k1_tarski(E_236))=k1_enumset1(A_234, B_235, E_236))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1696])).
% 3.38/1.60  tff(c_18, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.38/1.60  tff(c_14, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.38/1.60  tff(c_22, plain, (![A_18, B_19]: (r1_xboole_0(A_18, B_19) | k4_xboole_0(A_18, B_19)!=A_18)), inference(cnfTransformation, [status(thm)], [f_65])).
% 3.38/1.60  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.38/1.60  tff(c_189, plain, (![A_92, B_93, C_94]: (~r1_xboole_0(A_92, B_93) | ~r2_hidden(C_94, k3_xboole_0(A_92, B_93)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.38/1.60  tff(c_206, plain, (![A_97, B_98]: (~r1_xboole_0(A_97, B_98) | k3_xboole_0(A_97, B_98)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_189])).
% 3.38/1.60  tff(c_561, plain, (![A_121, B_122]: (k3_xboole_0(A_121, B_122)=k1_xboole_0 | k4_xboole_0(A_121, B_122)!=A_121)), inference(resolution, [status(thm)], [c_22, c_206])).
% 3.38/1.60  tff(c_580, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_14, c_561])).
% 3.38/1.60  tff(c_309, plain, (![A_105, B_106]: (k4_xboole_0(A_105, k4_xboole_0(A_105, B_106))=k3_xboole_0(A_105, B_106))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.38/1.60  tff(c_327, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_309])).
% 3.38/1.60  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.38/1.60  tff(c_155, plain, (![A_89, B_90]: (k5_xboole_0(A_89, k3_xboole_0(A_89, B_90))=k4_xboole_0(A_89, B_90))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.38/1.60  tff(c_167, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_155])).
% 3.38/1.60  tff(c_332, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k3_xboole_0(A_1, k1_xboole_0))), inference(demodulation, [status(thm), theory('equality')], [c_327, c_167])).
% 3.38/1.60  tff(c_70, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_108])).
% 3.38/1.60  tff(c_111, plain, (![A_76, B_77]: (k3_xboole_0(A_76, B_77)=A_76 | ~r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.38/1.60  tff(c_115, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_70, c_111])).
% 3.38/1.60  tff(c_164, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_115, c_155])).
% 3.38/1.60  tff(c_409, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k3_xboole_0(k1_tarski('#skF_5'), k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_332, c_164])).
% 3.38/1.60  tff(c_24, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_67])).
% 3.38/1.60  tff(c_416, plain, (k5_xboole_0(k2_tarski('#skF_6', '#skF_7'), k3_xboole_0(k1_tarski('#skF_5'), k1_xboole_0))=k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_409, c_24])).
% 3.38/1.60  tff(c_771, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_580, c_416])).
% 3.38/1.60  tff(c_1707, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_1701, c_771])).
% 3.38/1.60  tff(c_28, plain, (![E_28, A_22, B_23]: (r2_hidden(E_28, k1_enumset1(A_22, B_23, E_28)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.38/1.60  tff(c_1737, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_1707, c_28])).
% 3.38/1.60  tff(c_840, plain, (![E_145, C_146, B_147, A_148]: (E_145=C_146 | E_145=B_147 | E_145=A_148 | ~r2_hidden(E_145, k1_enumset1(A_148, B_147, C_146)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.38/1.60  tff(c_847, plain, (![E_145, B_36, A_35]: (E_145=B_36 | E_145=A_35 | E_145=A_35 | ~r2_hidden(E_145, k2_tarski(A_35, B_36)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_840])).
% 3.38/1.60  tff(c_1746, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_1737, c_847])).
% 3.38/1.60  tff(c_1753, plain, $false, inference(negUnitSimplification, [status(thm)], [c_68, c_68, c_66, c_1746])).
% 3.38/1.60  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.38/1.60  
% 3.38/1.60  Inference rules
% 3.38/1.60  ----------------------
% 3.38/1.60  #Ref     : 0
% 3.38/1.60  #Sup     : 381
% 3.38/1.60  #Fact    : 2
% 3.38/1.60  #Define  : 0
% 3.38/1.60  #Split   : 2
% 3.38/1.60  #Chain   : 0
% 3.38/1.60  #Close   : 0
% 3.38/1.60  
% 3.38/1.60  Ordering : KBO
% 3.38/1.60  
% 3.38/1.60  Simplification rules
% 3.38/1.60  ----------------------
% 3.38/1.60  #Subsume      : 56
% 3.38/1.60  #Demod        : 259
% 3.38/1.60  #Tautology    : 228
% 3.38/1.60  #SimpNegUnit  : 18
% 3.38/1.60  #BackRed      : 12
% 3.38/1.60  
% 3.38/1.60  #Partial instantiations: 0
% 3.38/1.60  #Strategies tried      : 1
% 3.38/1.60  
% 3.38/1.60  Timing (in seconds)
% 3.38/1.60  ----------------------
% 3.38/1.61  Preprocessing        : 0.35
% 3.38/1.61  Parsing              : 0.18
% 3.38/1.61  CNF conversion       : 0.03
% 3.38/1.61  Main loop            : 0.49
% 3.38/1.61  Inferencing          : 0.18
% 3.38/1.61  Reduction            : 0.17
% 3.38/1.61  Demodulation         : 0.12
% 3.38/1.61  BG Simplification    : 0.03
% 3.38/1.61  Subsumption          : 0.08
% 3.38/1.61  Abstraction          : 0.03
% 3.38/1.61  MUC search           : 0.00
% 3.38/1.61  Cooper               : 0.00
% 3.38/1.61  Total                : 0.87
% 3.38/1.61  Index Insertion      : 0.00
% 3.38/1.61  Index Deletion       : 0.00
% 3.38/1.61  Index Matching       : 0.00
% 3.38/1.61  BG Taut test         : 0.00
%------------------------------------------------------------------------------

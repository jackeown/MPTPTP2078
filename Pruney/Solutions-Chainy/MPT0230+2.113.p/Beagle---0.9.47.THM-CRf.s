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

% Result     : Theorem 3.18s
% Output     : CNFRefutation 3.18s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 104 expanded)
%              Number of leaves         :   41 (  53 expanded)
%              Depth                    :   12
%              Number of atoms          :   77 ( 117 expanded)
%              Number of equality atoms :   56 (  81 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

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

tff(f_104,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_86,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_84,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_88,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_80,axiom,(
    ! [A,B,C,D,E] : k3_enumset1(A,B,C,D,E) = k2_xboole_0(k2_enumset1(A,B,C,D),k1_tarski(E)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t50_enumset1)).

tff(f_57,axiom,(
    ! [A] : k4_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_boole)).

tff(f_61,axiom,(
    ! [A] : r1_xboole_0(A,k1_xboole_0) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t65_xboole_1)).

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

tff(f_51,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_59,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_78,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_64,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_62,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_52,plain,(
    ! [A_35,B_36,C_37] : k2_enumset1(A_35,A_35,B_36,C_37) = k1_enumset1(A_35,B_36,C_37) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_50,plain,(
    ! [A_33,B_34] : k1_enumset1(A_33,A_33,B_34) = k2_tarski(A_33,B_34) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_54,plain,(
    ! [A_38,B_39,C_40,D_41] : k3_enumset1(A_38,A_38,B_39,C_40,D_41) = k2_enumset1(A_38,B_39,C_40,D_41) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_654,plain,(
    ! [A_139,E_137,D_136,B_138,C_135] : k2_xboole_0(k2_enumset1(A_139,B_138,C_135,D_136),k1_tarski(E_137)) = k3_enumset1(A_139,B_138,C_135,D_136,E_137) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_663,plain,(
    ! [A_35,B_36,C_37,E_137] : k3_enumset1(A_35,A_35,B_36,C_37,E_137) = k2_xboole_0(k1_enumset1(A_35,B_36,C_37),k1_tarski(E_137)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_654])).

tff(c_758,plain,(
    ! [A_146,B_147,C_148,E_149] : k2_xboole_0(k1_enumset1(A_146,B_147,C_148),k1_tarski(E_149)) = k2_enumset1(A_146,B_147,C_148,E_149) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_663])).

tff(c_767,plain,(
    ! [A_33,B_34,E_149] : k2_xboole_0(k2_tarski(A_33,B_34),k1_tarski(E_149)) = k2_enumset1(A_33,A_33,B_34,E_149) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_758])).

tff(c_780,plain,(
    ! [A_156,B_157,E_158] : k2_xboole_0(k2_tarski(A_156,B_157),k1_tarski(E_158)) = k1_enumset1(A_156,B_157,E_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_767])).

tff(c_14,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_18,plain,(
    ! [A_17] : r1_xboole_0(A_17,k1_xboole_0) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_8,plain,(
    ! [A_8] :
      ( r2_hidden('#skF_2'(A_8),A_8)
      | k1_xboole_0 = A_8 ) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_133,plain,(
    ! [A_83,B_84,C_85] :
      ( ~ r1_xboole_0(A_83,B_84)
      | ~ r2_hidden(C_85,k3_xboole_0(A_83,B_84)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_161,plain,(
    ! [A_89,B_90] :
      ( ~ r1_xboole_0(A_89,B_90)
      | k3_xboole_0(A_89,B_90) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_133])).

tff(c_165,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_161])).

tff(c_292,plain,(
    ! [A_99,B_100] : k5_xboole_0(A_99,k3_xboole_0(A_99,B_100)) = k4_xboole_0(A_99,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_309,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = k4_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_292])).

tff(c_318,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_309])).

tff(c_219,plain,(
    ! [A_95,B_96] : k4_xboole_0(A_95,k4_xboole_0(A_95,B_96)) = k3_xboole_0(A_95,B_96) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_237,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_219])).

tff(c_240,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_237])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_315,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_292])).

tff(c_319,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_240,c_315])).

tff(c_66,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_123,plain,(
    ! [A_79,B_80] :
      ( k3_xboole_0(A_79,B_80) = A_79
      | ~ r1_tarski(A_79,B_80) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_127,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_123])).

tff(c_312,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_292])).

tff(c_399,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_319,c_312])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_406,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k5_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_399,c_20])).

tff(c_410,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_318,c_406])).

tff(c_786,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_780,c_410])).

tff(c_24,plain,(
    ! [E_26,A_20,B_21] : r2_hidden(E_26,k1_enumset1(A_20,B_21,E_26)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_814,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_786,c_24])).

tff(c_538,plain,(
    ! [E_119,C_120,B_121,A_122] :
      ( E_119 = C_120
      | E_119 = B_121
      | E_119 = A_122
      | ~ r2_hidden(E_119,k1_enumset1(A_122,B_121,C_120)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_545,plain,(
    ! [E_119,B_34,A_33] :
      ( E_119 = B_34
      | E_119 = A_33
      | E_119 = A_33
      | ~ r2_hidden(E_119,k2_tarski(A_33,B_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_538])).

tff(c_823,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_814,c_545])).

tff(c_827,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_64,c_62,c_823])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n015.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 14:01:08 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.18/1.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.51  
% 3.18/1.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.51  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 3.18/1.51  
% 3.18/1.51  %Foreground sorts:
% 3.18/1.51  
% 3.18/1.51  
% 3.18/1.51  %Background operators:
% 3.18/1.51  
% 3.18/1.51  
% 3.18/1.51  %Foreground operators:
% 3.18/1.51  tff('#skF_2', type, '#skF_2': $i > $i).
% 3.18/1.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.18/1.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.18/1.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.18/1.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.18/1.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.18/1.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.18/1.51  tff('#skF_7', type, '#skF_7': $i).
% 3.18/1.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.18/1.51  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.18/1.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.18/1.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.18/1.51  tff('#skF_5', type, '#skF_5': $i).
% 3.18/1.51  tff('#skF_6', type, '#skF_6': $i).
% 3.18/1.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.18/1.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 3.18/1.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.51  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 3.18/1.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.18/1.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.18/1.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.18/1.51  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 3.18/1.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.18/1.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.18/1.51  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 3.18/1.51  
% 3.18/1.53  tff(f_104, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.18/1.53  tff(f_86, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.18/1.53  tff(f_84, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.18/1.53  tff(f_88, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.18/1.53  tff(f_80, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 3.18/1.53  tff(f_57, axiom, (![A]: (k4_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_boole)).
% 3.18/1.53  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.18/1.53  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.18/1.53  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.18/1.53  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.18/1.53  tff(f_59, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.18/1.53  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.18/1.53  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.18/1.53  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.18/1.53  tff(f_78, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.18/1.53  tff(c_64, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.18/1.53  tff(c_62, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.18/1.53  tff(c_52, plain, (![A_35, B_36, C_37]: (k2_enumset1(A_35, A_35, B_36, C_37)=k1_enumset1(A_35, B_36, C_37))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.18/1.53  tff(c_50, plain, (![A_33, B_34]: (k1_enumset1(A_33, A_33, B_34)=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_84])).
% 3.18/1.53  tff(c_54, plain, (![A_38, B_39, C_40, D_41]: (k3_enumset1(A_38, A_38, B_39, C_40, D_41)=k2_enumset1(A_38, B_39, C_40, D_41))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.18/1.53  tff(c_654, plain, (![A_139, E_137, D_136, B_138, C_135]: (k2_xboole_0(k2_enumset1(A_139, B_138, C_135, D_136), k1_tarski(E_137))=k3_enumset1(A_139, B_138, C_135, D_136, E_137))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.18/1.53  tff(c_663, plain, (![A_35, B_36, C_37, E_137]: (k3_enumset1(A_35, A_35, B_36, C_37, E_137)=k2_xboole_0(k1_enumset1(A_35, B_36, C_37), k1_tarski(E_137)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_654])).
% 3.18/1.53  tff(c_758, plain, (![A_146, B_147, C_148, E_149]: (k2_xboole_0(k1_enumset1(A_146, B_147, C_148), k1_tarski(E_149))=k2_enumset1(A_146, B_147, C_148, E_149))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_663])).
% 3.18/1.53  tff(c_767, plain, (![A_33, B_34, E_149]: (k2_xboole_0(k2_tarski(A_33, B_34), k1_tarski(E_149))=k2_enumset1(A_33, A_33, B_34, E_149))), inference(superposition, [status(thm), theory('equality')], [c_50, c_758])).
% 3.18/1.53  tff(c_780, plain, (![A_156, B_157, E_158]: (k2_xboole_0(k2_tarski(A_156, B_157), k1_tarski(E_158))=k1_enumset1(A_156, B_157, E_158))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_767])).
% 3.18/1.53  tff(c_14, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.18/1.53  tff(c_18, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.18/1.53  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.18/1.53  tff(c_133, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, k3_xboole_0(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.18/1.53  tff(c_161, plain, (![A_89, B_90]: (~r1_xboole_0(A_89, B_90) | k3_xboole_0(A_89, B_90)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_133])).
% 3.18/1.53  tff(c_165, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_161])).
% 3.18/1.53  tff(c_292, plain, (![A_99, B_100]: (k5_xboole_0(A_99, k3_xboole_0(A_99, B_100))=k4_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.18/1.53  tff(c_309, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=k4_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_165, c_292])).
% 3.18/1.53  tff(c_318, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_309])).
% 3.18/1.53  tff(c_219, plain, (![A_95, B_96]: (k4_xboole_0(A_95, k4_xboole_0(A_95, B_96))=k3_xboole_0(A_95, B_96))), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.18/1.53  tff(c_237, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_219])).
% 3.18/1.53  tff(c_240, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_165, c_237])).
% 3.18/1.53  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.18/1.53  tff(c_315, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_292])).
% 3.18/1.53  tff(c_319, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_240, c_315])).
% 3.18/1.53  tff(c_66, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.18/1.53  tff(c_123, plain, (![A_79, B_80]: (k3_xboole_0(A_79, B_80)=A_79 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.18/1.53  tff(c_127, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_66, c_123])).
% 3.18/1.53  tff(c_312, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_292])).
% 3.18/1.53  tff(c_399, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_319, c_312])).
% 3.18/1.53  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.18/1.53  tff(c_406, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k5_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_399, c_20])).
% 3.18/1.53  tff(c_410, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_318, c_406])).
% 3.18/1.53  tff(c_786, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_780, c_410])).
% 3.18/1.53  tff(c_24, plain, (![E_26, A_20, B_21]: (r2_hidden(E_26, k1_enumset1(A_20, B_21, E_26)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.18/1.53  tff(c_814, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_786, c_24])).
% 3.18/1.53  tff(c_538, plain, (![E_119, C_120, B_121, A_122]: (E_119=C_120 | E_119=B_121 | E_119=A_122 | ~r2_hidden(E_119, k1_enumset1(A_122, B_121, C_120)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.18/1.53  tff(c_545, plain, (![E_119, B_34, A_33]: (E_119=B_34 | E_119=A_33 | E_119=A_33 | ~r2_hidden(E_119, k2_tarski(A_33, B_34)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_538])).
% 3.18/1.53  tff(c_823, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_814, c_545])).
% 3.18/1.53  tff(c_827, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_64, c_62, c_823])).
% 3.18/1.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.18/1.53  
% 3.18/1.53  Inference rules
% 3.18/1.53  ----------------------
% 3.18/1.53  #Ref     : 0
% 3.18/1.53  #Sup     : 177
% 3.18/1.53  #Fact    : 0
% 3.18/1.53  #Define  : 0
% 3.18/1.53  #Split   : 1
% 3.18/1.53  #Chain   : 0
% 3.18/1.53  #Close   : 0
% 3.18/1.53  
% 3.18/1.53  Ordering : KBO
% 3.18/1.53  
% 3.18/1.53  Simplification rules
% 3.18/1.53  ----------------------
% 3.18/1.53  #Subsume      : 7
% 3.18/1.53  #Demod        : 91
% 3.18/1.53  #Tautology    : 127
% 3.18/1.53  #SimpNegUnit  : 4
% 3.18/1.53  #BackRed      : 2
% 3.18/1.53  
% 3.18/1.53  #Partial instantiations: 0
% 3.18/1.53  #Strategies tried      : 1
% 3.18/1.53  
% 3.18/1.53  Timing (in seconds)
% 3.18/1.53  ----------------------
% 3.18/1.53  Preprocessing        : 0.33
% 3.18/1.53  Parsing              : 0.17
% 3.18/1.53  CNF conversion       : 0.03
% 3.18/1.53  Main loop            : 0.37
% 3.18/1.53  Inferencing          : 0.13
% 3.18/1.53  Reduction            : 0.13
% 3.18/1.53  Demodulation         : 0.10
% 3.18/1.53  BG Simplification    : 0.02
% 3.18/1.54  Subsumption          : 0.06
% 3.18/1.54  Abstraction          : 0.02
% 3.18/1.54  MUC search           : 0.00
% 3.18/1.54  Cooper               : 0.00
% 3.18/1.54  Total                : 0.75
% 3.18/1.54  Index Insertion      : 0.00
% 3.18/1.54  Index Deletion       : 0.00
% 3.18/1.54  Index Matching       : 0.00
% 3.18/1.54  BG Taut test         : 0.00
%------------------------------------------------------------------------------

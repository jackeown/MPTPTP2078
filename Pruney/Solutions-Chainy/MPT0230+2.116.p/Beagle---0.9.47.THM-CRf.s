%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n019.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:10 EST 2020

% Result     : Theorem 2.84s
% Output     : CNFRefutation 2.84s
% Verified   : 
% Statistics : Number of formulae       :   81 ( 104 expanded)
%              Number of leaves         :   41 (  53 expanded)
%              Depth                    :   15
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

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

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

tff(f_57,axiom,(
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

tff(c_756,plain,(
    ! [E_144,D_143,A_146,C_142,B_145] : k2_xboole_0(k2_enumset1(A_146,B_145,C_142,D_143),k1_tarski(E_144)) = k3_enumset1(A_146,B_145,C_142,D_143,E_144) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_765,plain,(
    ! [A_35,B_36,C_37,E_144] : k3_enumset1(A_35,A_35,B_36,C_37,E_144) = k2_xboole_0(k1_enumset1(A_35,B_36,C_37),k1_tarski(E_144)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_756])).

tff(c_769,plain,(
    ! [A_147,B_148,C_149,E_150] : k2_xboole_0(k1_enumset1(A_147,B_148,C_149),k1_tarski(E_150)) = k2_enumset1(A_147,B_148,C_149,E_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_765])).

tff(c_778,plain,(
    ! [A_33,B_34,E_150] : k2_xboole_0(k2_tarski(A_33,B_34),k1_tarski(E_150)) = k2_enumset1(A_33,A_33,B_34,E_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_769])).

tff(c_791,plain,(
    ! [A_157,B_158,E_159] : k2_xboole_0(k2_tarski(A_157,B_158),k1_tarski(E_159)) = k1_enumset1(A_157,B_158,E_159) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_778])).

tff(c_16,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

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

tff(c_215,plain,(
    ! [A_96,B_97] : k5_xboole_0(A_96,k3_xboole_0(A_96,B_97)) = k4_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_224,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = k4_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_215])).

tff(c_234,plain,(
    ! [A_98] : k4_xboole_0(A_98,k1_xboole_0) = A_98 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_224])).

tff(c_14,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_240,plain,(
    ! [A_98] : k4_xboole_0(A_98,A_98) = k3_xboole_0(A_98,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_14])).

tff(c_248,plain,(
    ! [A_98] : k4_xboole_0(A_98,A_98) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_240])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_230,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_215])).

tff(c_285,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_230])).

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

tff(c_227,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_215])).

tff(c_408,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_227])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_415,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k5_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_20])).

tff(c_419,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_415])).

tff(c_797,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_791,c_419])).

tff(c_24,plain,(
    ! [E_26,A_20,B_21] : r2_hidden(E_26,k1_enumset1(A_20,B_21,E_26)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_825,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_797,c_24])).

tff(c_497,plain,(
    ! [E_118,C_119,B_120,A_121] :
      ( E_118 = C_119
      | E_118 = B_120
      | E_118 = A_121
      | ~ r2_hidden(E_118,k1_enumset1(A_121,B_120,C_119)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_504,plain,(
    ! [E_118,B_34,A_33] :
      ( E_118 = B_34
      | E_118 = A_33
      | E_118 = A_33
      | ~ r2_hidden(E_118,k2_tarski(A_33,B_34)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_497])).

tff(c_834,plain,
    ( '#skF_7' = '#skF_5'
    | '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_825,c_504])).

tff(c_838,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_64,c_62,c_834])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n019.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 10:12:52 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.84/1.37  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.37  
% 2.84/1.37  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.38  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.84/1.38  
% 2.84/1.38  %Foreground sorts:
% 2.84/1.38  
% 2.84/1.38  
% 2.84/1.38  %Background operators:
% 2.84/1.38  
% 2.84/1.38  
% 2.84/1.38  %Foreground operators:
% 2.84/1.38  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.84/1.38  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.84/1.38  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.84/1.38  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.84/1.38  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.84/1.38  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.84/1.38  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.84/1.38  tff('#skF_7', type, '#skF_7': $i).
% 2.84/1.38  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.84/1.38  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.84/1.38  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.84/1.38  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.84/1.38  tff('#skF_5', type, '#skF_5': $i).
% 2.84/1.38  tff('#skF_6', type, '#skF_6': $i).
% 2.84/1.38  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.84/1.38  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.84/1.38  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.38  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.84/1.38  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.38  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.84/1.38  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.84/1.38  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.84/1.38  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.84/1.38  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.84/1.38  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.84/1.38  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.84/1.38  
% 2.84/1.39  tff(f_104, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 2.84/1.39  tff(f_86, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 2.84/1.39  tff(f_84, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 2.84/1.39  tff(f_88, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 2.84/1.39  tff(f_80, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 2.84/1.39  tff(f_59, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 2.84/1.39  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 2.84/1.39  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 2.84/1.39  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 2.84/1.39  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 2.84/1.39  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 2.84/1.39  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 2.84/1.39  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 2.84/1.39  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 2.84/1.39  tff(f_78, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 2.84/1.39  tff(c_64, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.84/1.39  tff(c_62, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.84/1.39  tff(c_52, plain, (![A_35, B_36, C_37]: (k2_enumset1(A_35, A_35, B_36, C_37)=k1_enumset1(A_35, B_36, C_37))), inference(cnfTransformation, [status(thm)], [f_86])).
% 2.84/1.39  tff(c_50, plain, (![A_33, B_34]: (k1_enumset1(A_33, A_33, B_34)=k2_tarski(A_33, B_34))), inference(cnfTransformation, [status(thm)], [f_84])).
% 2.84/1.39  tff(c_54, plain, (![A_38, B_39, C_40, D_41]: (k3_enumset1(A_38, A_38, B_39, C_40, D_41)=k2_enumset1(A_38, B_39, C_40, D_41))), inference(cnfTransformation, [status(thm)], [f_88])).
% 2.84/1.39  tff(c_756, plain, (![E_144, D_143, A_146, C_142, B_145]: (k2_xboole_0(k2_enumset1(A_146, B_145, C_142, D_143), k1_tarski(E_144))=k3_enumset1(A_146, B_145, C_142, D_143, E_144))), inference(cnfTransformation, [status(thm)], [f_80])).
% 2.84/1.39  tff(c_765, plain, (![A_35, B_36, C_37, E_144]: (k3_enumset1(A_35, A_35, B_36, C_37, E_144)=k2_xboole_0(k1_enumset1(A_35, B_36, C_37), k1_tarski(E_144)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_756])).
% 2.84/1.39  tff(c_769, plain, (![A_147, B_148, C_149, E_150]: (k2_xboole_0(k1_enumset1(A_147, B_148, C_149), k1_tarski(E_150))=k2_enumset1(A_147, B_148, C_149, E_150))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_765])).
% 2.84/1.39  tff(c_778, plain, (![A_33, B_34, E_150]: (k2_xboole_0(k2_tarski(A_33, B_34), k1_tarski(E_150))=k2_enumset1(A_33, A_33, B_34, E_150))), inference(superposition, [status(thm), theory('equality')], [c_50, c_769])).
% 2.84/1.39  tff(c_791, plain, (![A_157, B_158, E_159]: (k2_xboole_0(k2_tarski(A_157, B_158), k1_tarski(E_159))=k1_enumset1(A_157, B_158, E_159))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_778])).
% 2.84/1.39  tff(c_16, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_59])).
% 2.84/1.39  tff(c_18, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 2.84/1.39  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 2.84/1.39  tff(c_133, plain, (![A_83, B_84, C_85]: (~r1_xboole_0(A_83, B_84) | ~r2_hidden(C_85, k3_xboole_0(A_83, B_84)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 2.84/1.39  tff(c_161, plain, (![A_89, B_90]: (~r1_xboole_0(A_89, B_90) | k3_xboole_0(A_89, B_90)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_133])).
% 2.84/1.39  tff(c_165, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_161])).
% 2.84/1.39  tff(c_215, plain, (![A_96, B_97]: (k5_xboole_0(A_96, k3_xboole_0(A_96, B_97))=k4_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_51])).
% 2.84/1.39  tff(c_224, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=k4_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_165, c_215])).
% 2.84/1.39  tff(c_234, plain, (![A_98]: (k4_xboole_0(A_98, k1_xboole_0)=A_98)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_224])).
% 2.84/1.39  tff(c_14, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 2.84/1.39  tff(c_240, plain, (![A_98]: (k4_xboole_0(A_98, A_98)=k3_xboole_0(A_98, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_234, c_14])).
% 2.84/1.39  tff(c_248, plain, (![A_98]: (k4_xboole_0(A_98, A_98)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_165, c_240])).
% 2.84/1.39  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 2.84/1.39  tff(c_230, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_215])).
% 2.84/1.39  tff(c_285, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_248, c_230])).
% 2.84/1.39  tff(c_66, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 2.84/1.39  tff(c_123, plain, (![A_79, B_80]: (k3_xboole_0(A_79, B_80)=A_79 | ~r1_tarski(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_55])).
% 2.84/1.39  tff(c_127, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_66, c_123])).
% 2.84/1.39  tff(c_227, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_215])).
% 2.84/1.39  tff(c_408, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_285, c_227])).
% 2.84/1.39  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 2.84/1.39  tff(c_415, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k5_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_408, c_20])).
% 2.84/1.39  tff(c_419, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_415])).
% 2.84/1.39  tff(c_797, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_791, c_419])).
% 2.84/1.39  tff(c_24, plain, (![E_26, A_20, B_21]: (r2_hidden(E_26, k1_enumset1(A_20, B_21, E_26)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.84/1.39  tff(c_825, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_797, c_24])).
% 2.84/1.39  tff(c_497, plain, (![E_118, C_119, B_120, A_121]: (E_118=C_119 | E_118=B_120 | E_118=A_121 | ~r2_hidden(E_118, k1_enumset1(A_121, B_120, C_119)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 2.84/1.39  tff(c_504, plain, (![E_118, B_34, A_33]: (E_118=B_34 | E_118=A_33 | E_118=A_33 | ~r2_hidden(E_118, k2_tarski(A_33, B_34)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_497])).
% 2.84/1.39  tff(c_834, plain, ('#skF_7'='#skF_5' | '#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_825, c_504])).
% 2.84/1.39  tff(c_838, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_64, c_62, c_834])).
% 2.84/1.39  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.84/1.39  
% 2.84/1.39  Inference rules
% 2.84/1.39  ----------------------
% 2.84/1.39  #Ref     : 0
% 2.84/1.39  #Sup     : 181
% 2.84/1.39  #Fact    : 0
% 2.84/1.39  #Define  : 0
% 2.84/1.39  #Split   : 1
% 2.84/1.39  #Chain   : 0
% 2.84/1.39  #Close   : 0
% 2.84/1.39  
% 2.84/1.39  Ordering : KBO
% 2.84/1.39  
% 2.84/1.39  Simplification rules
% 2.84/1.39  ----------------------
% 2.84/1.39  #Subsume      : 7
% 2.84/1.39  #Demod        : 105
% 2.84/1.39  #Tautology    : 124
% 2.84/1.39  #SimpNegUnit  : 4
% 2.84/1.39  #BackRed      : 1
% 2.84/1.39  
% 2.84/1.39  #Partial instantiations: 0
% 2.84/1.39  #Strategies tried      : 1
% 2.84/1.39  
% 2.84/1.39  Timing (in seconds)
% 2.84/1.39  ----------------------
% 2.84/1.40  Preprocessing        : 0.33
% 2.84/1.40  Parsing              : 0.17
% 2.84/1.40  CNF conversion       : 0.02
% 2.84/1.40  Main loop            : 0.32
% 2.84/1.40  Inferencing          : 0.12
% 2.84/1.40  Reduction            : 0.11
% 2.84/1.40  Demodulation         : 0.08
% 2.84/1.40  BG Simplification    : 0.02
% 2.84/1.40  Subsumption          : 0.05
% 2.84/1.40  Abstraction          : 0.02
% 2.84/1.40  MUC search           : 0.00
% 2.84/1.40  Cooper               : 0.00
% 2.84/1.40  Total                : 0.69
% 2.84/1.40  Index Insertion      : 0.00
% 2.84/1.40  Index Deletion       : 0.00
% 2.84/1.40  Index Matching       : 0.00
% 2.84/1.40  BG Taut test         : 0.00
%------------------------------------------------------------------------------

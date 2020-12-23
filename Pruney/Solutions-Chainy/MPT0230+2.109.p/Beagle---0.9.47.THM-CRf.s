%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n021.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:09 EST 2020

% Result     : Theorem 2.63s
% Output     : CNFRefutation 3.01s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 106 expanded)
%              Number of leaves         :   41 (  53 expanded)
%              Depth                    :   15
%              Number of atoms          :   80 ( 120 expanded)
%              Number of equality atoms :   59 (  84 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(f_88,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_86,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_90,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_82,axiom,(
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

tff(f_80,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(c_62,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_64,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_54,plain,(
    ! [A_38,B_39,C_40] : k2_enumset1(A_38,A_38,B_39,C_40) = k1_enumset1(A_38,B_39,C_40) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_52,plain,(
    ! [A_36,B_37] : k1_enumset1(A_36,A_36,B_37) = k2_tarski(A_36,B_37) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_56,plain,(
    ! [A_41,B_42,C_43,D_44] : k3_enumset1(A_41,A_41,B_42,C_43,D_44) = k2_enumset1(A_41,B_42,C_43,D_44) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_787,plain,(
    ! [B_140,A_141,D_143,E_142,C_139] : k2_xboole_0(k2_enumset1(A_141,B_140,C_139,D_143),k1_tarski(E_142)) = k3_enumset1(A_141,B_140,C_139,D_143,E_142) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_796,plain,(
    ! [A_38,B_39,C_40,E_142] : k3_enumset1(A_38,A_38,B_39,C_40,E_142) = k2_xboole_0(k1_enumset1(A_38,B_39,C_40),k1_tarski(E_142)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_787])).

tff(c_832,plain,(
    ! [A_147,B_148,C_149,E_150] : k2_xboole_0(k1_enumset1(A_147,B_148,C_149),k1_tarski(E_150)) = k2_enumset1(A_147,B_148,C_149,E_150) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_796])).

tff(c_850,plain,(
    ! [A_36,B_37,E_150] : k2_xboole_0(k2_tarski(A_36,B_37),k1_tarski(E_150)) = k2_enumset1(A_36,A_36,B_37,E_150) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_832])).

tff(c_854,plain,(
    ! [A_151,B_152,E_153] : k2_xboole_0(k2_tarski(A_151,B_152),k1_tarski(E_153)) = k1_enumset1(A_151,B_152,E_153) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_850])).

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
    ! [A_79,B_80,C_81] :
      ( ~ r1_xboole_0(A_79,B_80)
      | ~ r2_hidden(C_81,k3_xboole_0(A_79,B_80)) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_161,plain,(
    ! [A_85,B_86] :
      ( ~ r1_xboole_0(A_85,B_86)
      | k3_xboole_0(A_85,B_86) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_8,c_133])).

tff(c_165,plain,(
    ! [A_17] : k3_xboole_0(A_17,k1_xboole_0) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_18,c_161])).

tff(c_203,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k3_xboole_0(A_90,B_91)) = k4_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_212,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = k4_xboole_0(A_17,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_165,c_203])).

tff(c_234,plain,(
    ! [A_94] : k4_xboole_0(A_94,k1_xboole_0) = A_94 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_212])).

tff(c_14,plain,(
    ! [A_14,B_15] : k4_xboole_0(A_14,k4_xboole_0(A_14,B_15)) = k3_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_243,plain,(
    ! [A_94] : k4_xboole_0(A_94,A_94) = k3_xboole_0(A_94,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_234,c_14])).

tff(c_248,plain,(
    ! [A_94] : k4_xboole_0(A_94,A_94) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_165,c_243])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_218,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_203])).

tff(c_285,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_248,c_218])).

tff(c_66,plain,(
    r1_tarski(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(cnfTransformation,[status(thm)],[f_104])).

tff(c_123,plain,(
    ! [A_75,B_76] :
      ( k3_xboole_0(A_75,B_76) = A_75
      | ~ r1_tarski(A_75,B_76) ) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_127,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_123])).

tff(c_215,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_127,c_203])).

tff(c_482,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_6','#skF_7')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_285,c_215])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_486,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k5_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_482,c_20])).

tff(c_492,plain,(
    k2_xboole_0(k2_tarski('#skF_6','#skF_7'),k1_tarski('#skF_5')) = k2_tarski('#skF_6','#skF_7') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_486])).

tff(c_860,plain,(
    k1_enumset1('#skF_6','#skF_7','#skF_5') = k2_tarski('#skF_6','#skF_7') ),
    inference(superposition,[status(thm),theory(equality)],[c_854,c_492])).

tff(c_24,plain,(
    ! [E_26,A_20,B_21] : r2_hidden(E_26,k1_enumset1(A_20,B_21,E_26)) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_888,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_6','#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_860,c_24])).

tff(c_350,plain,(
    ! [C_99,B_100,A_101] : k1_enumset1(C_99,B_100,A_101) = k1_enumset1(A_101,B_100,C_99) ),
    inference(cnfTransformation,[status(thm)],[f_80])).

tff(c_366,plain,(
    ! [C_99,B_100] : k1_enumset1(C_99,B_100,B_100) = k2_tarski(B_100,C_99) ),
    inference(superposition,[status(thm),theory(equality)],[c_350,c_52])).

tff(c_585,plain,(
    ! [E_117,C_118,B_119,A_120] :
      ( E_117 = C_118
      | E_117 = B_119
      | E_117 = A_120
      | ~ r2_hidden(E_117,k1_enumset1(A_120,B_119,C_118)) ) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_592,plain,(
    ! [E_117,B_100,C_99] :
      ( E_117 = B_100
      | E_117 = B_100
      | E_117 = C_99
      | ~ r2_hidden(E_117,k2_tarski(B_100,C_99)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_366,c_585])).

tff(c_906,plain,
    ( '#skF_5' = '#skF_6'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_888,c_592])).

tff(c_913,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_62,c_64,c_64,c_906])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n021.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:07:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 2.63/1.45  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.45  
% 2.63/1.45  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 2.63/1.46  %$ r2_hidden > r1_xboole_0 > r1_tarski > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_7 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 2.63/1.46  
% 2.63/1.46  %Foreground sorts:
% 2.63/1.46  
% 2.63/1.46  
% 2.63/1.46  %Background operators:
% 2.63/1.46  
% 2.63/1.46  
% 2.63/1.46  %Foreground operators:
% 2.63/1.46  tff('#skF_2', type, '#skF_2': $i > $i).
% 2.63/1.46  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 2.63/1.46  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 2.63/1.46  tff(k1_tarski, type, k1_tarski: $i > $i).
% 2.63/1.46  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 2.63/1.46  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 2.63/1.46  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 2.63/1.46  tff('#skF_7', type, '#skF_7': $i).
% 2.63/1.46  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 2.63/1.46  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 2.63/1.46  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 2.63/1.46  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 2.63/1.46  tff('#skF_5', type, '#skF_5': $i).
% 2.63/1.46  tff('#skF_6', type, '#skF_6': $i).
% 2.63/1.46  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 2.63/1.46  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 2.63/1.46  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.46  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 2.63/1.46  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 2.63/1.46  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 2.63/1.46  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 2.63/1.46  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 2.63/1.46  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 2.63/1.46  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 2.63/1.46  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 2.63/1.46  
% 3.01/1.47  tff(f_104, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 3.01/1.47  tff(f_88, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.01/1.47  tff(f_86, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.01/1.47  tff(f_90, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 3.01/1.47  tff(f_82, axiom, (![A, B, C, D, E]: (k3_enumset1(A, B, C, D, E) = k2_xboole_0(k2_enumset1(A, B, C, D), k1_tarski(E)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t50_enumset1)).
% 3.01/1.47  tff(f_59, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.01/1.47  tff(f_61, axiom, (![A]: r1_xboole_0(A, k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t65_xboole_1)).
% 3.01/1.47  tff(f_49, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 3.01/1.47  tff(f_41, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 3.01/1.47  tff(f_51, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.01/1.47  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.01/1.47  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.01/1.47  tff(f_55, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.01/1.47  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.01/1.47  tff(f_78, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.01/1.47  tff(f_80, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 3.01/1.47  tff(c_62, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.01/1.47  tff(c_64, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.01/1.47  tff(c_54, plain, (![A_38, B_39, C_40]: (k2_enumset1(A_38, A_38, B_39, C_40)=k1_enumset1(A_38, B_39, C_40))), inference(cnfTransformation, [status(thm)], [f_88])).
% 3.01/1.47  tff(c_52, plain, (![A_36, B_37]: (k1_enumset1(A_36, A_36, B_37)=k2_tarski(A_36, B_37))), inference(cnfTransformation, [status(thm)], [f_86])).
% 3.01/1.47  tff(c_56, plain, (![A_41, B_42, C_43, D_44]: (k3_enumset1(A_41, A_41, B_42, C_43, D_44)=k2_enumset1(A_41, B_42, C_43, D_44))), inference(cnfTransformation, [status(thm)], [f_90])).
% 3.01/1.47  tff(c_787, plain, (![B_140, A_141, D_143, E_142, C_139]: (k2_xboole_0(k2_enumset1(A_141, B_140, C_139, D_143), k1_tarski(E_142))=k3_enumset1(A_141, B_140, C_139, D_143, E_142))), inference(cnfTransformation, [status(thm)], [f_82])).
% 3.01/1.47  tff(c_796, plain, (![A_38, B_39, C_40, E_142]: (k3_enumset1(A_38, A_38, B_39, C_40, E_142)=k2_xboole_0(k1_enumset1(A_38, B_39, C_40), k1_tarski(E_142)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_787])).
% 3.01/1.47  tff(c_832, plain, (![A_147, B_148, C_149, E_150]: (k2_xboole_0(k1_enumset1(A_147, B_148, C_149), k1_tarski(E_150))=k2_enumset1(A_147, B_148, C_149, E_150))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_796])).
% 3.01/1.47  tff(c_850, plain, (![A_36, B_37, E_150]: (k2_xboole_0(k2_tarski(A_36, B_37), k1_tarski(E_150))=k2_enumset1(A_36, A_36, B_37, E_150))), inference(superposition, [status(thm), theory('equality')], [c_52, c_832])).
% 3.01/1.47  tff(c_854, plain, (![A_151, B_152, E_153]: (k2_xboole_0(k2_tarski(A_151, B_152), k1_tarski(E_153))=k1_enumset1(A_151, B_152, E_153))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_850])).
% 3.01/1.47  tff(c_16, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_59])).
% 3.01/1.47  tff(c_18, plain, (![A_17]: (r1_xboole_0(A_17, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_61])).
% 3.01/1.47  tff(c_8, plain, (![A_8]: (r2_hidden('#skF_2'(A_8), A_8) | k1_xboole_0=A_8)), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.01/1.47  tff(c_133, plain, (![A_79, B_80, C_81]: (~r1_xboole_0(A_79, B_80) | ~r2_hidden(C_81, k3_xboole_0(A_79, B_80)))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.01/1.47  tff(c_161, plain, (![A_85, B_86]: (~r1_xboole_0(A_85, B_86) | k3_xboole_0(A_85, B_86)=k1_xboole_0)), inference(resolution, [status(thm)], [c_8, c_133])).
% 3.01/1.47  tff(c_165, plain, (![A_17]: (k3_xboole_0(A_17, k1_xboole_0)=k1_xboole_0)), inference(resolution, [status(thm)], [c_18, c_161])).
% 3.01/1.47  tff(c_203, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k3_xboole_0(A_90, B_91))=k4_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_51])).
% 3.01/1.47  tff(c_212, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=k4_xboole_0(A_17, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_165, c_203])).
% 3.01/1.47  tff(c_234, plain, (![A_94]: (k4_xboole_0(A_94, k1_xboole_0)=A_94)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_212])).
% 3.01/1.47  tff(c_14, plain, (![A_14, B_15]: (k4_xboole_0(A_14, k4_xboole_0(A_14, B_15))=k3_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_57])).
% 3.01/1.47  tff(c_243, plain, (![A_94]: (k4_xboole_0(A_94, A_94)=k3_xboole_0(A_94, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_234, c_14])).
% 3.01/1.47  tff(c_248, plain, (![A_94]: (k4_xboole_0(A_94, A_94)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_165, c_243])).
% 3.01/1.47  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 3.01/1.47  tff(c_218, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_203])).
% 3.01/1.47  tff(c_285, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_248, c_218])).
% 3.01/1.47  tff(c_66, plain, (r1_tarski(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(cnfTransformation, [status(thm)], [f_104])).
% 3.01/1.47  tff(c_123, plain, (![A_75, B_76]: (k3_xboole_0(A_75, B_76)=A_75 | ~r1_tarski(A_75, B_76))), inference(cnfTransformation, [status(thm)], [f_55])).
% 3.01/1.47  tff(c_127, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_66, c_123])).
% 3.01/1.47  tff(c_215, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_127, c_203])).
% 3.01/1.47  tff(c_482, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_6', '#skF_7'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_285, c_215])).
% 3.01/1.47  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_63])).
% 3.01/1.47  tff(c_486, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k5_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_482, c_20])).
% 3.01/1.47  tff(c_492, plain, (k2_xboole_0(k2_tarski('#skF_6', '#skF_7'), k1_tarski('#skF_5'))=k2_tarski('#skF_6', '#skF_7')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_486])).
% 3.01/1.47  tff(c_860, plain, (k1_enumset1('#skF_6', '#skF_7', '#skF_5')=k2_tarski('#skF_6', '#skF_7')), inference(superposition, [status(thm), theory('equality')], [c_854, c_492])).
% 3.01/1.47  tff(c_24, plain, (![E_26, A_20, B_21]: (r2_hidden(E_26, k1_enumset1(A_20, B_21, E_26)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.01/1.47  tff(c_888, plain, (r2_hidden('#skF_5', k2_tarski('#skF_6', '#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_860, c_24])).
% 3.01/1.47  tff(c_350, plain, (![C_99, B_100, A_101]: (k1_enumset1(C_99, B_100, A_101)=k1_enumset1(A_101, B_100, C_99))), inference(cnfTransformation, [status(thm)], [f_80])).
% 3.01/1.47  tff(c_366, plain, (![C_99, B_100]: (k1_enumset1(C_99, B_100, B_100)=k2_tarski(B_100, C_99))), inference(superposition, [status(thm), theory('equality')], [c_350, c_52])).
% 3.01/1.47  tff(c_585, plain, (![E_117, C_118, B_119, A_120]: (E_117=C_118 | E_117=B_119 | E_117=A_120 | ~r2_hidden(E_117, k1_enumset1(A_120, B_119, C_118)))), inference(cnfTransformation, [status(thm)], [f_78])).
% 3.01/1.47  tff(c_592, plain, (![E_117, B_100, C_99]: (E_117=B_100 | E_117=B_100 | E_117=C_99 | ~r2_hidden(E_117, k2_tarski(B_100, C_99)))), inference(superposition, [status(thm), theory('equality')], [c_366, c_585])).
% 3.01/1.47  tff(c_906, plain, ('#skF_5'='#skF_6' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_888, c_592])).
% 3.01/1.47  tff(c_913, plain, $false, inference(negUnitSimplification, [status(thm)], [c_62, c_64, c_64, c_906])).
% 3.01/1.47  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.01/1.47  
% 3.01/1.47  Inference rules
% 3.01/1.47  ----------------------
% 3.01/1.47  #Ref     : 0
% 3.01/1.47  #Sup     : 198
% 3.01/1.47  #Fact    : 0
% 3.01/1.47  #Define  : 0
% 3.01/1.47  #Split   : 1
% 3.01/1.47  #Chain   : 0
% 3.01/1.47  #Close   : 0
% 3.01/1.47  
% 3.01/1.47  Ordering : KBO
% 3.01/1.47  
% 3.01/1.47  Simplification rules
% 3.01/1.47  ----------------------
% 3.01/1.47  #Subsume      : 8
% 3.01/1.47  #Demod        : 87
% 3.01/1.47  #Tautology    : 139
% 3.01/1.47  #SimpNegUnit  : 4
% 3.01/1.47  #BackRed      : 1
% 3.01/1.47  
% 3.01/1.47  #Partial instantiations: 0
% 3.01/1.47  #Strategies tried      : 1
% 3.01/1.47  
% 3.01/1.47  Timing (in seconds)
% 3.01/1.47  ----------------------
% 3.01/1.47  Preprocessing        : 0.39
% 3.01/1.47  Parsing              : 0.19
% 3.01/1.47  CNF conversion       : 0.03
% 3.01/1.47  Main loop            : 0.36
% 3.01/1.47  Inferencing          : 0.13
% 3.01/1.47  Reduction            : 0.12
% 3.01/1.47  Demodulation         : 0.09
% 3.01/1.48  BG Simplification    : 0.02
% 3.01/1.48  Subsumption          : 0.06
% 3.01/1.48  Abstraction          : 0.02
% 3.01/1.48  MUC search           : 0.00
% 3.01/1.48  Cooper               : 0.00
% 3.01/1.48  Total                : 0.79
% 3.01/1.48  Index Insertion      : 0.00
% 3.01/1.48  Index Deletion       : 0.00
% 3.01/1.48  Index Matching       : 0.00
% 3.01/1.48  BG Taut test         : 0.00
%------------------------------------------------------------------------------

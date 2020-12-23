%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n006.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:54 EST 2020

% Result     : Theorem 4.32s
% Output     : CNFRefutation 4.32s
% Verified   : 
% Statistics : Number of formulae       :   91 ( 241 expanded)
%              Number of leaves         :   41 (  98 expanded)
%              Depth                    :   19
%              Number of atoms          :   89 ( 293 expanded)
%              Number of equality atoms :   63 ( 203 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1

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

tff(f_103,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t24_zfmisc_1)).

tff(f_88,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_86,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_90,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_84,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_63,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_65,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => r1_xboole_0(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',symmetry_r1_xboole_0)).

tff(f_53,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_45,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_59,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_64,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_52,plain,(
    ! [A_35,B_36] : k1_enumset1(A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_50,plain,(
    ! [A_34] : k2_tarski(A_34,A_34) = k1_tarski(A_34) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_54,plain,(
    ! [A_37,B_38,C_39] : k2_enumset1(A_37,A_37,B_38,C_39) = k1_enumset1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_1242,plain,(
    ! [A_142,B_143,C_144,D_145] : k2_xboole_0(k1_enumset1(A_142,B_143,C_144),k1_tarski(D_145)) = k2_enumset1(A_142,B_143,C_144,D_145) ),
    inference(cnfTransformation,[status(thm)],[f_84])).

tff(c_1251,plain,(
    ! [A_35,B_36,D_145] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(D_145)) = k2_enumset1(A_35,A_35,B_36,D_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1242])).

tff(c_1483,plain,(
    ! [A_156,B_157,D_158] : k2_xboole_0(k2_tarski(A_156,B_157),k1_tarski(D_158)) = k1_enumset1(A_156,B_157,D_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1251])).

tff(c_1492,plain,(
    ! [A_34,D_158] : k2_xboole_0(k1_tarski(A_34),k1_tarski(D_158)) = k1_enumset1(A_34,A_34,D_158) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_1483])).

tff(c_1495,plain,(
    ! [A_34,D_158] : k2_xboole_0(k1_tarski(A_34),k1_tarski(D_158)) = k2_tarski(A_34,D_158) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1492])).

tff(c_1505,plain,(
    ! [A_164,D_165] : k2_xboole_0(k1_tarski(A_164),k1_tarski(D_165)) = k2_tarski(A_164,D_165) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_1492])).

tff(c_18,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_20,plain,(
    ! [A_19,B_20] : r1_xboole_0(k4_xboole_0(A_19,B_20),B_20) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_96,plain,(
    ! [B_68,A_69] :
      ( r1_xboole_0(B_68,A_69)
      | ~ r1_xboole_0(A_69,B_68) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_99,plain,(
    ! [B_20,A_19] : r1_xboole_0(B_20,k4_xboole_0(A_19,B_20)) ),
    inference(resolution,[status(thm)],[c_20,c_96])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_229,plain,(
    ! [A_99,B_100,C_101] :
      ( ~ r1_xboole_0(A_99,B_100)
      | ~ r2_hidden(C_101,k3_xboole_0(A_99,B_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_305,plain,(
    ! [A_107,B_108] :
      ( ~ r1_xboole_0(A_107,B_108)
      | k3_xboole_0(A_107,B_108) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_229])).

tff(c_329,plain,(
    ! [B_20,A_19] : k3_xboole_0(B_20,k4_xboole_0(A_19,B_20)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_305])).

tff(c_331,plain,(
    ! [B_109,A_110] : k3_xboole_0(B_109,k4_xboole_0(A_110,B_109)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_99,c_305])).

tff(c_12,plain,(
    ! [A_12,B_13] : k5_xboole_0(A_12,k3_xboole_0(A_12,B_13)) = k4_xboole_0(A_12,B_13) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_339,plain,(
    ! [B_109,A_110] : k4_xboole_0(B_109,k4_xboole_0(A_110,B_109)) = k5_xboole_0(B_109,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_12])).

tff(c_397,plain,(
    ! [B_113,A_114] : k4_xboole_0(B_113,k4_xboole_0(A_114,B_113)) = B_113 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_339])).

tff(c_16,plain,(
    ! [A_16,B_17] : k4_xboole_0(A_16,k4_xboole_0(A_16,B_17)) = k3_xboole_0(A_16,B_17) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_421,plain,(
    ! [B_113,A_114] : k3_xboole_0(B_113,k4_xboole_0(A_114,B_113)) = k4_xboole_0(B_113,B_113) ),
    inference(superposition,[status(thm),theory(equality)],[c_397,c_16])).

tff(c_453,plain,(
    ! [B_113] : k4_xboole_0(B_113,B_113) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_329,c_421])).

tff(c_2,plain,(
    ! [A_1] : k3_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_197,plain,(
    ! [A_96,B_97] : k5_xboole_0(A_96,k3_xboole_0(A_96,B_97)) = k4_xboole_0(A_96,B_97) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_209,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k4_xboole_0(A_1,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_197])).

tff(c_497,plain,(
    ! [A_1] : k5_xboole_0(A_1,A_1) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_453,c_209])).

tff(c_66,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_103])).

tff(c_131,plain,(
    ! [A_86,B_87] :
      ( k3_xboole_0(A_86,B_87) = A_86
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_135,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_66,c_131])).

tff(c_206,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_135,c_197])).

tff(c_827,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_497,c_206])).

tff(c_22,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_844,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_827,c_22])).

tff(c_865,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_844])).

tff(c_1511,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_1505,c_865])).

tff(c_1254,plain,(
    ! [A_35,B_36,D_145] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(D_145)) = k1_enumset1(A_35,B_36,D_145) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_1251])).

tff(c_1533,plain,(
    ! [D_145] : k2_xboole_0(k1_tarski('#skF_6'),k1_tarski(D_145)) = k1_enumset1('#skF_6','#skF_5',D_145) ),
    inference(superposition,[status(thm),theory(equality)],[c_1511,c_1254])).

tff(c_1546,plain,(
    ! [D_166] : k1_enumset1('#skF_6','#skF_5',D_166) = k2_tarski('#skF_6',D_166) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1495,c_1533])).

tff(c_28,plain,(
    ! [E_29,A_23,C_25] : r2_hidden(E_29,k1_enumset1(A_23,E_29,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_1558,plain,(
    ! [D_166] : r2_hidden('#skF_5',k2_tarski('#skF_6',D_166)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1546,c_28])).

tff(c_1452,plain,(
    ! [E_152,C_153,B_154,A_155] :
      ( E_152 = C_153
      | E_152 = B_154
      | E_152 = A_155
      | ~ r2_hidden(E_152,k1_enumset1(A_155,B_154,C_153)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_2558,plain,(
    ! [E_205,B_206,A_207] :
      ( E_205 = B_206
      | E_205 = A_207
      | E_205 = A_207
      | ~ r2_hidden(E_205,k2_tarski(A_207,B_206)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_1452])).

tff(c_2561,plain,(
    ! [D_166] :
      ( D_166 = '#skF_5'
      | '#skF_5' = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_1558,c_2558])).

tff(c_2592,plain,(
    '#skF_5' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_64,c_2561])).

tff(c_2584,plain,(
    ! [D_166] : D_166 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_64,c_2561])).

tff(c_2897,plain,(
    ! [D_4569] : D_4569 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_2592,c_2584])).

tff(c_3190,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_2897,c_64])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.10/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.10/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n006.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 20:24:22 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.32/1.80  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.80  
% 4.32/1.80  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.80  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 4.32/1.80  
% 4.32/1.80  %Foreground sorts:
% 4.32/1.80  
% 4.32/1.80  
% 4.32/1.80  %Background operators:
% 4.32/1.80  
% 4.32/1.80  
% 4.32/1.80  %Foreground operators:
% 4.32/1.80  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.32/1.80  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.32/1.80  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.32/1.80  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.32/1.80  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.32/1.80  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.32/1.80  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.32/1.80  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.32/1.80  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.32/1.80  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.32/1.80  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.32/1.80  tff('#skF_5', type, '#skF_5': $i).
% 4.32/1.80  tff('#skF_6', type, '#skF_6': $i).
% 4.32/1.80  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.32/1.80  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.32/1.80  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.32/1.80  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.32/1.80  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.32/1.80  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.32/1.80  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.32/1.80  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.32/1.80  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.32/1.80  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.32/1.80  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.32/1.80  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.32/1.80  
% 4.32/1.82  tff(f_103, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t24_zfmisc_1)).
% 4.32/1.82  tff(f_88, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.32/1.82  tff(f_86, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.32/1.82  tff(f_90, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.32/1.82  tff(f_84, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 4.32/1.82  tff(f_63, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.32/1.82  tff(f_65, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t79_xboole_1)).
% 4.32/1.82  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) => r1_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', symmetry_r1_xboole_0)).
% 4.32/1.82  tff(f_53, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.32/1.82  tff(f_45, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.32/1.82  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.32/1.82  tff(f_61, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.32/1.82  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.32/1.82  tff(f_59, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.32/1.82  tff(f_67, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.32/1.82  tff(f_82, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.32/1.82  tff(c_64, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.32/1.82  tff(c_52, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.32/1.82  tff(c_50, plain, (![A_34]: (k2_tarski(A_34, A_34)=k1_tarski(A_34))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.32/1.82  tff(c_54, plain, (![A_37, B_38, C_39]: (k2_enumset1(A_37, A_37, B_38, C_39)=k1_enumset1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.32/1.82  tff(c_1242, plain, (![A_142, B_143, C_144, D_145]: (k2_xboole_0(k1_enumset1(A_142, B_143, C_144), k1_tarski(D_145))=k2_enumset1(A_142, B_143, C_144, D_145))), inference(cnfTransformation, [status(thm)], [f_84])).
% 4.32/1.82  tff(c_1251, plain, (![A_35, B_36, D_145]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(D_145))=k2_enumset1(A_35, A_35, B_36, D_145))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1242])).
% 4.32/1.82  tff(c_1483, plain, (![A_156, B_157, D_158]: (k2_xboole_0(k2_tarski(A_156, B_157), k1_tarski(D_158))=k1_enumset1(A_156, B_157, D_158))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1251])).
% 4.32/1.82  tff(c_1492, plain, (![A_34, D_158]: (k2_xboole_0(k1_tarski(A_34), k1_tarski(D_158))=k1_enumset1(A_34, A_34, D_158))), inference(superposition, [status(thm), theory('equality')], [c_50, c_1483])).
% 4.32/1.82  tff(c_1495, plain, (![A_34, D_158]: (k2_xboole_0(k1_tarski(A_34), k1_tarski(D_158))=k2_tarski(A_34, D_158))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1492])).
% 4.32/1.82  tff(c_1505, plain, (![A_164, D_165]: (k2_xboole_0(k1_tarski(A_164), k1_tarski(D_165))=k2_tarski(A_164, D_165))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_1492])).
% 4.32/1.82  tff(c_18, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.32/1.82  tff(c_20, plain, (![A_19, B_20]: (r1_xboole_0(k4_xboole_0(A_19, B_20), B_20))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.32/1.82  tff(c_96, plain, (![B_68, A_69]: (r1_xboole_0(B_68, A_69) | ~r1_xboole_0(A_69, B_68))), inference(cnfTransformation, [status(thm)], [f_31])).
% 4.32/1.82  tff(c_99, plain, (![B_20, A_19]: (r1_xboole_0(B_20, k4_xboole_0(A_19, B_20)))), inference(resolution, [status(thm)], [c_20, c_96])).
% 4.32/1.82  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.32/1.82  tff(c_229, plain, (![A_99, B_100, C_101]: (~r1_xboole_0(A_99, B_100) | ~r2_hidden(C_101, k3_xboole_0(A_99, B_100)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 4.32/1.82  tff(c_305, plain, (![A_107, B_108]: (~r1_xboole_0(A_107, B_108) | k3_xboole_0(A_107, B_108)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_229])).
% 4.32/1.82  tff(c_329, plain, (![B_20, A_19]: (k3_xboole_0(B_20, k4_xboole_0(A_19, B_20))=k1_xboole_0)), inference(resolution, [status(thm)], [c_99, c_305])).
% 4.32/1.82  tff(c_331, plain, (![B_109, A_110]: (k3_xboole_0(B_109, k4_xboole_0(A_110, B_109))=k1_xboole_0)), inference(resolution, [status(thm)], [c_99, c_305])).
% 4.32/1.82  tff(c_12, plain, (![A_12, B_13]: (k5_xboole_0(A_12, k3_xboole_0(A_12, B_13))=k4_xboole_0(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.32/1.82  tff(c_339, plain, (![B_109, A_110]: (k4_xboole_0(B_109, k4_xboole_0(A_110, B_109))=k5_xboole_0(B_109, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_331, c_12])).
% 4.32/1.82  tff(c_397, plain, (![B_113, A_114]: (k4_xboole_0(B_113, k4_xboole_0(A_114, B_113))=B_113)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_339])).
% 4.32/1.82  tff(c_16, plain, (![A_16, B_17]: (k4_xboole_0(A_16, k4_xboole_0(A_16, B_17))=k3_xboole_0(A_16, B_17))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.32/1.82  tff(c_421, plain, (![B_113, A_114]: (k3_xboole_0(B_113, k4_xboole_0(A_114, B_113))=k4_xboole_0(B_113, B_113))), inference(superposition, [status(thm), theory('equality')], [c_397, c_16])).
% 4.32/1.82  tff(c_453, plain, (![B_113]: (k4_xboole_0(B_113, B_113)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_329, c_421])).
% 4.32/1.82  tff(c_2, plain, (![A_1]: (k3_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.32/1.82  tff(c_197, plain, (![A_96, B_97]: (k5_xboole_0(A_96, k3_xboole_0(A_96, B_97))=k4_xboole_0(A_96, B_97))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.32/1.82  tff(c_209, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k4_xboole_0(A_1, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_197])).
% 4.32/1.82  tff(c_497, plain, (![A_1]: (k5_xboole_0(A_1, A_1)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_453, c_209])).
% 4.32/1.82  tff(c_66, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_103])).
% 4.32/1.82  tff(c_131, plain, (![A_86, B_87]: (k3_xboole_0(A_86, B_87)=A_86 | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.32/1.82  tff(c_135, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_66, c_131])).
% 4.32/1.82  tff(c_206, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_135, c_197])).
% 4.32/1.82  tff(c_827, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_497, c_206])).
% 4.32/1.82  tff(c_22, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.32/1.82  tff(c_844, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_827, c_22])).
% 4.32/1.82  tff(c_865, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_844])).
% 4.32/1.82  tff(c_1511, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_1505, c_865])).
% 4.32/1.82  tff(c_1254, plain, (![A_35, B_36, D_145]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(D_145))=k1_enumset1(A_35, B_36, D_145))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_1251])).
% 4.32/1.82  tff(c_1533, plain, (![D_145]: (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski(D_145))=k1_enumset1('#skF_6', '#skF_5', D_145))), inference(superposition, [status(thm), theory('equality')], [c_1511, c_1254])).
% 4.32/1.82  tff(c_1546, plain, (![D_166]: (k1_enumset1('#skF_6', '#skF_5', D_166)=k2_tarski('#skF_6', D_166))), inference(demodulation, [status(thm), theory('equality')], [c_1495, c_1533])).
% 4.32/1.82  tff(c_28, plain, (![E_29, A_23, C_25]: (r2_hidden(E_29, k1_enumset1(A_23, E_29, C_25)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.32/1.82  tff(c_1558, plain, (![D_166]: (r2_hidden('#skF_5', k2_tarski('#skF_6', D_166)))), inference(superposition, [status(thm), theory('equality')], [c_1546, c_28])).
% 4.32/1.82  tff(c_1452, plain, (![E_152, C_153, B_154, A_155]: (E_152=C_153 | E_152=B_154 | E_152=A_155 | ~r2_hidden(E_152, k1_enumset1(A_155, B_154, C_153)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.32/1.82  tff(c_2558, plain, (![E_205, B_206, A_207]: (E_205=B_206 | E_205=A_207 | E_205=A_207 | ~r2_hidden(E_205, k2_tarski(A_207, B_206)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_1452])).
% 4.32/1.82  tff(c_2561, plain, (![D_166]: (D_166='#skF_5' | '#skF_5'='#skF_6')), inference(resolution, [status(thm)], [c_1558, c_2558])).
% 4.32/1.82  tff(c_2592, plain, ('#skF_5'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_64, c_64, c_2561])).
% 4.32/1.82  tff(c_2584, plain, (![D_166]: (D_166='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_64, c_64, c_2561])).
% 4.32/1.82  tff(c_2897, plain, (![D_4569]: (D_4569='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_2592, c_2584])).
% 4.32/1.82  tff(c_3190, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_2897, c_64])).
% 4.32/1.82  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.32/1.82  
% 4.32/1.82  Inference rules
% 4.32/1.82  ----------------------
% 4.32/1.82  #Ref     : 0
% 4.32/1.82  #Sup     : 887
% 4.32/1.82  #Fact    : 0
% 4.32/1.82  #Define  : 0
% 4.32/1.82  #Split   : 1
% 4.32/1.82  #Chain   : 0
% 4.32/1.82  #Close   : 0
% 4.32/1.82  
% 4.32/1.82  Ordering : KBO
% 4.32/1.82  
% 4.32/1.82  Simplification rules
% 4.32/1.82  ----------------------
% 4.32/1.82  #Subsume      : 108
% 4.32/1.82  #Demod        : 668
% 4.32/1.82  #Tautology    : 500
% 4.32/1.82  #SimpNegUnit  : 16
% 4.32/1.82  #BackRed      : 3
% 4.32/1.82  
% 4.32/1.82  #Partial instantiations: 79
% 4.32/1.82  #Strategies tried      : 1
% 4.32/1.82  
% 4.32/1.82  Timing (in seconds)
% 4.32/1.82  ----------------------
% 4.50/1.82  Preprocessing        : 0.35
% 4.50/1.82  Parsing              : 0.18
% 4.50/1.82  CNF conversion       : 0.02
% 4.50/1.82  Main loop            : 0.71
% 4.50/1.82  Inferencing          : 0.27
% 4.50/1.82  Reduction            : 0.27
% 4.50/1.82  Demodulation         : 0.21
% 4.50/1.82  BG Simplification    : 0.03
% 4.50/1.82  Subsumption          : 0.10
% 4.50/1.82  Abstraction          : 0.03
% 4.50/1.82  MUC search           : 0.00
% 4.50/1.82  Cooper               : 0.00
% 4.50/1.82  Total                : 1.09
% 4.50/1.82  Index Insertion      : 0.00
% 4.50/1.82  Index Deletion       : 0.00
% 4.50/1.82  Index Matching       : 0.00
% 4.50/1.82  BG Taut test         : 0.00
%------------------------------------------------------------------------------

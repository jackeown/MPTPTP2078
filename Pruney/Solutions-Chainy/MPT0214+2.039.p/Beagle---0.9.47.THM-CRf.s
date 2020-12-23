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
% DateTime   : Thu Dec  3 09:47:34 EST 2020

% Result     : Theorem 4.81s
% Output     : CNFRefutation 4.81s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 249 expanded)
%              Number of leaves         :   41 ( 102 expanded)
%              Depth                    :   17
%              Number of atoms          :   89 ( 287 expanded)
%              Number of equality atoms :   66 ( 235 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

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

tff(f_105,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_90,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_88,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_92,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_86,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_67,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_65,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_63,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k4_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t83_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_82,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_68,plain,(
    '#skF_5' != '#skF_6' ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_56,plain,(
    ! [A_40,B_41] : k1_enumset1(A_40,A_40,B_41) = k2_tarski(A_40,B_41) ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_54,plain,(
    ! [A_39] : k2_tarski(A_39,A_39) = k1_tarski(A_39) ),
    inference(cnfTransformation,[status(thm)],[f_88])).

tff(c_58,plain,(
    ! [A_42,B_43,C_44] : k2_enumset1(A_42,A_42,B_43,C_44) = k1_enumset1(A_42,B_43,C_44) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_1083,plain,(
    ! [A_156,B_157,C_158,D_159] : k2_xboole_0(k1_enumset1(A_156,B_157,C_158),k1_tarski(D_159)) = k2_enumset1(A_156,B_157,C_158,D_159) ),
    inference(cnfTransformation,[status(thm)],[f_86])).

tff(c_1092,plain,(
    ! [A_40,B_41,D_159] : k2_xboole_0(k2_tarski(A_40,B_41),k1_tarski(D_159)) = k2_enumset1(A_40,A_40,B_41,D_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1083])).

tff(c_3302,plain,(
    ! [A_263,B_264,D_265] : k2_xboole_0(k2_tarski(A_263,B_264),k1_tarski(D_265)) = k1_enumset1(A_263,B_264,D_265) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1092])).

tff(c_3323,plain,(
    ! [A_39,D_265] : k2_xboole_0(k1_tarski(A_39),k1_tarski(D_265)) = k1_enumset1(A_39,A_39,D_265) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_3302])).

tff(c_3326,plain,(
    ! [A_39,D_265] : k2_xboole_0(k1_tarski(A_39),k1_tarski(D_265)) = k2_tarski(A_39,D_265) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3323])).

tff(c_3327,plain,(
    ! [A_266,D_267] : k2_xboole_0(k1_tarski(A_266),k1_tarski(D_267)) = k2_tarski(A_266,D_267) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_3323])).

tff(c_16,plain,(
    ! [A_16] : k5_xboole_0(A_16,k1_xboole_0) = A_16 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_155,plain,(
    ! [A_94,B_95] : k5_xboole_0(A_94,k3_xboole_0(A_94,B_95)) = k4_xboole_0(A_94,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_167,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_155])).

tff(c_2,plain,(
    ! [A_1] : k2_xboole_0(A_1,A_1) = A_1 ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_24,plain,(
    ! [A_22,B_23] : k5_xboole_0(A_22,k4_xboole_0(B_23,A_22)) = k2_xboole_0(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_67])).

tff(c_276,plain,(
    ! [A_115,B_116,C_117] : k5_xboole_0(k5_xboole_0(A_115,B_116),C_117) = k5_xboole_0(A_115,k5_xboole_0(B_116,C_117)) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_536,plain,(
    ! [A_134,C_135] : k5_xboole_0(k4_xboole_0(A_134,A_134),C_135) = k5_xboole_0(A_134,k5_xboole_0(A_134,C_135)) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_276])).

tff(c_580,plain,(
    ! [A_134] : k5_xboole_0(A_134,k5_xboole_0(A_134,k4_xboole_0(A_134,A_134))) = k4_xboole_0(k4_xboole_0(A_134,A_134),k4_xboole_0(A_134,A_134)) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_536])).

tff(c_875,plain,(
    ! [A_148] : k4_xboole_0(k4_xboole_0(A_148,A_148),k4_xboole_0(A_148,A_148)) = k4_xboole_0(A_148,A_148) ),
    inference(demodulation,[status(thm),theory(equality)],[c_167,c_2,c_24,c_580])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_20,plain,(
    ! [A_17,B_18] :
      ( r1_xboole_0(A_17,B_18)
      | k4_xboole_0(A_17,B_18) != A_17 ) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_205,plain,(
    ! [A_99,B_100,C_101] :
      ( ~ r1_xboole_0(A_99,B_100)
      | ~ r2_hidden(C_101,k3_xboole_0(A_99,B_100)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_226,plain,(
    ! [A_105,C_106] :
      ( ~ r1_xboole_0(A_105,A_105)
      | ~ r2_hidden(C_106,A_105) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_205])).

tff(c_236,plain,(
    ! [C_109,B_110] :
      ( ~ r2_hidden(C_109,B_110)
      | k4_xboole_0(B_110,B_110) != B_110 ) ),
    inference(resolution,[status(thm)],[c_20,c_226])).

tff(c_257,plain,(
    ! [A_10] :
      ( k4_xboole_0(A_10,A_10) != A_10
      | k1_xboole_0 = A_10 ) ),
    inference(resolution,[status(thm)],[c_10,c_236])).

tff(c_923,plain,(
    ! [A_148] : k4_xboole_0(A_148,A_148) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_875,c_257])).

tff(c_70,plain,(
    r1_tarski(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(cnfTransformation,[status(thm)],[f_105])).

tff(c_140,plain,(
    ! [A_90,B_91] :
      ( k3_xboole_0(A_90,B_91) = A_90
      | ~ r1_tarski(A_90,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_144,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_70,c_140])).

tff(c_164,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_144,c_155])).

tff(c_494,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_167,c_164])).

tff(c_965,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_6')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_923,c_494])).

tff(c_974,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k5_xboole_0(k1_tarski('#skF_6'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_965,c_24])).

tff(c_978,plain,(
    k2_xboole_0(k1_tarski('#skF_6'),k1_tarski('#skF_5')) = k1_tarski('#skF_6') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_974])).

tff(c_3345,plain,(
    k2_tarski('#skF_6','#skF_5') = k1_tarski('#skF_6') ),
    inference(superposition,[status(thm),theory(equality)],[c_3327,c_978])).

tff(c_1095,plain,(
    ! [A_40,B_41,D_159] : k2_xboole_0(k2_tarski(A_40,B_41),k1_tarski(D_159)) = k1_enumset1(A_40,B_41,D_159) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1092])).

tff(c_3367,plain,(
    ! [D_159] : k2_xboole_0(k1_tarski('#skF_6'),k1_tarski(D_159)) = k1_enumset1('#skF_6','#skF_5',D_159) ),
    inference(superposition,[status(thm),theory(equality)],[c_3345,c_1095])).

tff(c_3386,plain,(
    ! [D_268] : k1_enumset1('#skF_6','#skF_5',D_268) = k2_tarski('#skF_6',D_268) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3326,c_3367])).

tff(c_30,plain,(
    ! [E_30,A_24,C_26] : r2_hidden(E_30,k1_enumset1(A_24,E_30,C_26)) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3403,plain,(
    ! [D_268] : r2_hidden('#skF_5',k2_tarski('#skF_6',D_268)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3386,c_30])).

tff(c_845,plain,(
    ! [E_144,C_145,B_146,A_147] :
      ( E_144 = C_145
      | E_144 = B_146
      | E_144 = A_147
      | ~ r2_hidden(E_144,k1_enumset1(A_147,B_146,C_145)) ) ),
    inference(cnfTransformation,[status(thm)],[f_82])).

tff(c_3431,plain,(
    ! [E_270,B_271,A_272] :
      ( E_270 = B_271
      | E_270 = A_272
      | E_270 = A_272
      | ~ r2_hidden(E_270,k2_tarski(A_272,B_271)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_845])).

tff(c_3434,plain,(
    ! [D_268] :
      ( D_268 = '#skF_5'
      | '#skF_5' = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_3403,c_3431])).

tff(c_3477,plain,(
    '#skF_5' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_68,c_3434])).

tff(c_3465,plain,(
    ! [D_268] : D_268 = '#skF_5' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_68,c_3434])).

tff(c_3840,plain,(
    ! [D_5624] : D_5624 = '#skF_6' ),
    inference(superposition,[status(thm),theory(equality)],[c_3477,c_3465])).

tff(c_4192,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_3840,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.33  % Computer   : n006.cluster.edu
% 0.13/0.33  % Model      : x86_64 x86_64
% 0.13/0.33  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.33  % Memory     : 8042.1875MB
% 0.13/0.33  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.33  % CPULimit   : 60
% 0.13/0.33  % DateTime   : Tue Dec  1 15:02:37 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.81/1.82  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.83  
% 4.81/1.83  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.83  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_5 > #skF_6 > #skF_4 > #skF_3 > #skF_1
% 4.81/1.83  
% 4.81/1.83  %Foreground sorts:
% 4.81/1.83  
% 4.81/1.83  
% 4.81/1.83  %Background operators:
% 4.81/1.83  
% 4.81/1.83  
% 4.81/1.83  %Foreground operators:
% 4.81/1.83  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.81/1.83  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.81/1.83  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.81/1.83  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.81/1.83  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.81/1.83  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.81/1.83  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.81/1.83  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.81/1.83  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.81/1.83  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.81/1.83  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.81/1.83  tff('#skF_5', type, '#skF_5': $i).
% 4.81/1.83  tff('#skF_6', type, '#skF_6': $i).
% 4.81/1.83  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.81/1.83  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.81/1.83  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.81/1.83  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.81/1.83  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.81/1.83  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.81/1.83  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.81/1.83  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.81/1.83  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.81/1.83  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.81/1.83  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.81/1.83  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.81/1.83  
% 4.81/1.85  tff(f_105, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 4.81/1.85  tff(f_90, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t70_enumset1)).
% 4.81/1.85  tff(f_88, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.81/1.85  tff(f_92, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t71_enumset1)).
% 4.81/1.85  tff(f_86, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t46_enumset1)).
% 4.81/1.85  tff(f_59, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.81/1.85  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.81/1.85  tff(f_53, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.81/1.85  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 4.81/1.85  tff(f_67, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.81/1.85  tff(f_65, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.81/1.85  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.81/1.85  tff(f_63, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k4_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t83_xboole_1)).
% 4.81/1.85  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.81/1.85  tff(f_57, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.81/1.85  tff(f_82, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d1_enumset1)).
% 4.81/1.85  tff(c_68, plain, ('#skF_5'!='#skF_6'), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.81/1.85  tff(c_56, plain, (![A_40, B_41]: (k1_enumset1(A_40, A_40, B_41)=k2_tarski(A_40, B_41))), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.81/1.85  tff(c_54, plain, (![A_39]: (k2_tarski(A_39, A_39)=k1_tarski(A_39))), inference(cnfTransformation, [status(thm)], [f_88])).
% 4.81/1.85  tff(c_58, plain, (![A_42, B_43, C_44]: (k2_enumset1(A_42, A_42, B_43, C_44)=k1_enumset1(A_42, B_43, C_44))), inference(cnfTransformation, [status(thm)], [f_92])).
% 4.81/1.85  tff(c_1083, plain, (![A_156, B_157, C_158, D_159]: (k2_xboole_0(k1_enumset1(A_156, B_157, C_158), k1_tarski(D_159))=k2_enumset1(A_156, B_157, C_158, D_159))), inference(cnfTransformation, [status(thm)], [f_86])).
% 4.81/1.85  tff(c_1092, plain, (![A_40, B_41, D_159]: (k2_xboole_0(k2_tarski(A_40, B_41), k1_tarski(D_159))=k2_enumset1(A_40, A_40, B_41, D_159))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1083])).
% 4.81/1.85  tff(c_3302, plain, (![A_263, B_264, D_265]: (k2_xboole_0(k2_tarski(A_263, B_264), k1_tarski(D_265))=k1_enumset1(A_263, B_264, D_265))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1092])).
% 4.81/1.85  tff(c_3323, plain, (![A_39, D_265]: (k2_xboole_0(k1_tarski(A_39), k1_tarski(D_265))=k1_enumset1(A_39, A_39, D_265))), inference(superposition, [status(thm), theory('equality')], [c_54, c_3302])).
% 4.81/1.85  tff(c_3326, plain, (![A_39, D_265]: (k2_xboole_0(k1_tarski(A_39), k1_tarski(D_265))=k2_tarski(A_39, D_265))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3323])).
% 4.81/1.85  tff(c_3327, plain, (![A_266, D_267]: (k2_xboole_0(k1_tarski(A_266), k1_tarski(D_267))=k2_tarski(A_266, D_267))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_3323])).
% 4.81/1.85  tff(c_16, plain, (![A_16]: (k5_xboole_0(A_16, k1_xboole_0)=A_16)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.81/1.85  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.81/1.85  tff(c_155, plain, (![A_94, B_95]: (k5_xboole_0(A_94, k3_xboole_0(A_94, B_95))=k4_xboole_0(A_94, B_95))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.81/1.85  tff(c_167, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_155])).
% 4.81/1.85  tff(c_2, plain, (![A_1]: (k2_xboole_0(A_1, A_1)=A_1)), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.81/1.85  tff(c_24, plain, (![A_22, B_23]: (k5_xboole_0(A_22, k4_xboole_0(B_23, A_22))=k2_xboole_0(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_67])).
% 4.81/1.85  tff(c_276, plain, (![A_115, B_116, C_117]: (k5_xboole_0(k5_xboole_0(A_115, B_116), C_117)=k5_xboole_0(A_115, k5_xboole_0(B_116, C_117)))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.81/1.85  tff(c_536, plain, (![A_134, C_135]: (k5_xboole_0(k4_xboole_0(A_134, A_134), C_135)=k5_xboole_0(A_134, k5_xboole_0(A_134, C_135)))), inference(superposition, [status(thm), theory('equality')], [c_167, c_276])).
% 4.81/1.85  tff(c_580, plain, (![A_134]: (k5_xboole_0(A_134, k5_xboole_0(A_134, k4_xboole_0(A_134, A_134)))=k4_xboole_0(k4_xboole_0(A_134, A_134), k4_xboole_0(A_134, A_134)))), inference(superposition, [status(thm), theory('equality')], [c_167, c_536])).
% 4.81/1.85  tff(c_875, plain, (![A_148]: (k4_xboole_0(k4_xboole_0(A_148, A_148), k4_xboole_0(A_148, A_148))=k4_xboole_0(A_148, A_148))), inference(demodulation, [status(thm), theory('equality')], [c_167, c_2, c_24, c_580])).
% 4.81/1.85  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.81/1.85  tff(c_20, plain, (![A_17, B_18]: (r1_xboole_0(A_17, B_18) | k4_xboole_0(A_17, B_18)!=A_17)), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.81/1.85  tff(c_205, plain, (![A_99, B_100, C_101]: (~r1_xboole_0(A_99, B_100) | ~r2_hidden(C_101, k3_xboole_0(A_99, B_100)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.81/1.85  tff(c_226, plain, (![A_105, C_106]: (~r1_xboole_0(A_105, A_105) | ~r2_hidden(C_106, A_105))), inference(superposition, [status(thm), theory('equality')], [c_4, c_205])).
% 4.81/1.85  tff(c_236, plain, (![C_109, B_110]: (~r2_hidden(C_109, B_110) | k4_xboole_0(B_110, B_110)!=B_110)), inference(resolution, [status(thm)], [c_20, c_226])).
% 4.81/1.85  tff(c_257, plain, (![A_10]: (k4_xboole_0(A_10, A_10)!=A_10 | k1_xboole_0=A_10)), inference(resolution, [status(thm)], [c_10, c_236])).
% 4.81/1.85  tff(c_923, plain, (![A_148]: (k4_xboole_0(A_148, A_148)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_875, c_257])).
% 4.81/1.85  tff(c_70, plain, (r1_tarski(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(cnfTransformation, [status(thm)], [f_105])).
% 4.81/1.85  tff(c_140, plain, (![A_90, B_91]: (k3_xboole_0(A_90, B_91)=A_90 | ~r1_tarski(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.81/1.85  tff(c_144, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_70, c_140])).
% 4.81/1.85  tff(c_164, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_144, c_155])).
% 4.81/1.85  tff(c_494, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_167, c_164])).
% 4.81/1.85  tff(c_965, plain, (k4_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_6'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_923, c_494])).
% 4.81/1.85  tff(c_974, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k5_xboole_0(k1_tarski('#skF_6'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_965, c_24])).
% 4.81/1.85  tff(c_978, plain, (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski('#skF_5'))=k1_tarski('#skF_6')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_974])).
% 4.81/1.85  tff(c_3345, plain, (k2_tarski('#skF_6', '#skF_5')=k1_tarski('#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3327, c_978])).
% 4.81/1.85  tff(c_1095, plain, (![A_40, B_41, D_159]: (k2_xboole_0(k2_tarski(A_40, B_41), k1_tarski(D_159))=k1_enumset1(A_40, B_41, D_159))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1092])).
% 4.81/1.85  tff(c_3367, plain, (![D_159]: (k2_xboole_0(k1_tarski('#skF_6'), k1_tarski(D_159))=k1_enumset1('#skF_6', '#skF_5', D_159))), inference(superposition, [status(thm), theory('equality')], [c_3345, c_1095])).
% 4.81/1.85  tff(c_3386, plain, (![D_268]: (k1_enumset1('#skF_6', '#skF_5', D_268)=k2_tarski('#skF_6', D_268))), inference(demodulation, [status(thm), theory('equality')], [c_3326, c_3367])).
% 4.81/1.85  tff(c_30, plain, (![E_30, A_24, C_26]: (r2_hidden(E_30, k1_enumset1(A_24, E_30, C_26)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.81/1.85  tff(c_3403, plain, (![D_268]: (r2_hidden('#skF_5', k2_tarski('#skF_6', D_268)))), inference(superposition, [status(thm), theory('equality')], [c_3386, c_30])).
% 4.81/1.85  tff(c_845, plain, (![E_144, C_145, B_146, A_147]: (E_144=C_145 | E_144=B_146 | E_144=A_147 | ~r2_hidden(E_144, k1_enumset1(A_147, B_146, C_145)))), inference(cnfTransformation, [status(thm)], [f_82])).
% 4.81/1.85  tff(c_3431, plain, (![E_270, B_271, A_272]: (E_270=B_271 | E_270=A_272 | E_270=A_272 | ~r2_hidden(E_270, k2_tarski(A_272, B_271)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_845])).
% 4.81/1.85  tff(c_3434, plain, (![D_268]: (D_268='#skF_5' | '#skF_5'='#skF_6')), inference(resolution, [status(thm)], [c_3403, c_3431])).
% 4.81/1.85  tff(c_3477, plain, ('#skF_5'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_68, c_68, c_3434])).
% 4.81/1.85  tff(c_3465, plain, (![D_268]: (D_268='#skF_5')), inference(negUnitSimplification, [status(thm)], [c_68, c_68, c_3434])).
% 4.81/1.85  tff(c_3840, plain, (![D_5624]: (D_5624='#skF_6')), inference(superposition, [status(thm), theory('equality')], [c_3477, c_3465])).
% 4.81/1.85  tff(c_4192, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_3840, c_68])).
% 4.81/1.85  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.81/1.85  
% 4.81/1.85  Inference rules
% 4.81/1.85  ----------------------
% 4.81/1.85  #Ref     : 0
% 4.81/1.85  #Sup     : 1149
% 4.81/1.85  #Fact    : 0
% 4.81/1.85  #Define  : 0
% 4.81/1.85  #Split   : 1
% 4.81/1.85  #Chain   : 0
% 4.81/1.85  #Close   : 0
% 4.81/1.85  
% 4.81/1.85  Ordering : KBO
% 4.81/1.85  
% 4.81/1.85  Simplification rules
% 4.81/1.85  ----------------------
% 4.81/1.85  #Subsume      : 145
% 4.81/1.85  #Demod        : 626
% 4.81/1.85  #Tautology    : 564
% 4.81/1.85  #SimpNegUnit  : 8
% 4.81/1.85  #BackRed      : 10
% 4.81/1.85  
% 4.81/1.85  #Partial instantiations: 97
% 4.81/1.85  #Strategies tried      : 1
% 4.81/1.85  
% 4.81/1.85  Timing (in seconds)
% 4.81/1.85  ----------------------
% 4.81/1.85  Preprocessing        : 0.32
% 4.81/1.85  Parsing              : 0.16
% 4.81/1.85  CNF conversion       : 0.02
% 4.81/1.85  Main loop            : 0.81
% 4.81/1.85  Inferencing          : 0.32
% 4.81/1.85  Reduction            : 0.29
% 4.81/1.85  Demodulation         : 0.23
% 4.81/1.85  BG Simplification    : 0.04
% 4.81/1.85  Subsumption          : 0.11
% 4.81/1.85  Abstraction          : 0.04
% 4.81/1.85  MUC search           : 0.00
% 4.81/1.85  Cooper               : 0.00
% 4.81/1.85  Total                : 1.16
% 4.81/1.85  Index Insertion      : 0.00
% 4.81/1.85  Index Deletion       : 0.00
% 4.81/1.85  Index Matching       : 0.00
% 4.81/1.85  BG Taut test         : 0.00
%------------------------------------------------------------------------------

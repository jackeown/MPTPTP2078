%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n022.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:35 EST 2020

% Result     : Theorem 4.62s
% Output     : CNFRefutation 4.62s
% Verified   : 
% Statistics : Number of formulae       :   71 ( 178 expanded)
%              Number of leaves         :   34 (  75 expanded)
%              Depth                    :   14
%              Number of atoms          :   63 ( 197 expanded)
%              Number of equality atoms :   53 ( 171 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

%Foreground sorts:

%Background operators:

%Foreground operators:
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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_3',type,(
    '#skF_3': $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i * $i ) > $i )).

tff(f_77,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_62,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_60,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_39,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_54,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_56,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_44,plain,(
    ! [A_27,B_28] : k1_enumset1(A_27,A_27,B_28) = k2_tarski(A_27,B_28) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_42,plain,(
    ! [A_26] : k2_tarski(A_26,A_26) = k1_tarski(A_26) ),
    inference(cnfTransformation,[status(thm)],[f_60])).

tff(c_46,plain,(
    ! [A_29,B_30,C_31] : k2_enumset1(A_29,A_29,B_30,C_31) = k1_enumset1(A_29,B_30,C_31) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_558,plain,(
    ! [A_103,B_104,C_105,D_106] : k2_xboole_0(k1_enumset1(A_103,B_104,C_105),k1_tarski(D_106)) = k2_enumset1(A_103,B_104,C_105,D_106) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_600,plain,(
    ! [A_27,B_28,D_106] : k2_xboole_0(k2_tarski(A_27,B_28),k1_tarski(D_106)) = k2_enumset1(A_27,A_27,B_28,D_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_558])).

tff(c_609,plain,(
    ! [A_107,B_108,D_109] : k2_xboole_0(k2_tarski(A_107,B_108),k1_tarski(D_109)) = k1_enumset1(A_107,B_108,D_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_600])).

tff(c_639,plain,(
    ! [A_26,D_109] : k2_xboole_0(k1_tarski(A_26),k1_tarski(D_109)) = k1_enumset1(A_26,A_26,D_109) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_609])).

tff(c_647,plain,(
    ! [A_26,D_109] : k2_xboole_0(k1_tarski(A_26),k1_tarski(D_109)) = k2_tarski(A_26,D_109) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_639])).

tff(c_648,plain,(
    ! [A_110,D_111] : k2_xboole_0(k1_tarski(A_110),k1_tarski(D_111)) = k2_tarski(A_110,D_111) ),
    inference(demodulation,[status(thm),theory(equality)],[c_44,c_639])).

tff(c_10,plain,(
    ! [A_9] : k5_xboole_0(A_9,k1_xboole_0) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_8,plain,(
    ! [A_7,B_8] : k4_xboole_0(A_7,k2_xboole_0(A_7,B_8)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_307,plain,(
    ! [A_85,B_86] : k5_xboole_0(A_85,k3_xboole_0(A_85,B_86)) = k4_xboole_0(A_85,B_86) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_319,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_307])).

tff(c_322,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_319])).

tff(c_58,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_125,plain,(
    ! [A_76,B_77] :
      ( k3_xboole_0(A_76,B_77) = A_76
      | ~ r1_tarski(A_76,B_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_129,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_58,c_125])).

tff(c_316,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_129,c_307])).

tff(c_408,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_322,c_316])).

tff(c_12,plain,(
    ! [A_10,B_11] : k5_xboole_0(A_10,k4_xboole_0(B_11,A_10)) = k2_xboole_0(A_10,B_11) ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_412,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_408,c_12])).

tff(c_415,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_10,c_412])).

tff(c_663,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_648,c_415])).

tff(c_608,plain,(
    ! [A_27,B_28,D_106] : k2_xboole_0(k2_tarski(A_27,B_28),k1_tarski(D_106)) = k1_enumset1(A_27,B_28,D_106) ),
    inference(demodulation,[status(thm),theory(equality)],[c_46,c_600])).

tff(c_700,plain,(
    ! [D_106] : k2_xboole_0(k1_tarski('#skF_4'),k1_tarski(D_106)) = k1_enumset1('#skF_4','#skF_3',D_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_663,c_608])).

tff(c_774,plain,(
    ! [D_119] : k1_enumset1('#skF_4','#skF_3',D_119) = k2_tarski('#skF_4',D_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_647,c_700])).

tff(c_18,plain,(
    ! [E_18,A_12,C_14] : r2_hidden(E_18,k1_enumset1(A_12,E_18,C_14)) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_800,plain,(
    ! [D_119] : r2_hidden('#skF_3',k2_tarski('#skF_4',D_119)) ),
    inference(superposition,[status(thm),theory(equality)],[c_774,c_18])).

tff(c_713,plain,(
    ! [E_112,C_113,B_114,A_115] :
      ( E_112 = C_113
      | E_112 = B_114
      | E_112 = A_115
      | ~ r2_hidden(E_112,k1_enumset1(A_115,B_114,C_113)) ) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_2768,plain,(
    ! [E_218,B_219,A_220] :
      ( E_218 = B_219
      | E_218 = A_220
      | E_218 = A_220
      | ~ r2_hidden(E_218,k2_tarski(A_220,B_219)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_713])).

tff(c_2778,plain,(
    ! [D_119] :
      ( D_119 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_800,c_2768])).

tff(c_2800,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_2778])).

tff(c_2794,plain,(
    ! [D_119] : D_119 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_2778])).

tff(c_3187,plain,(
    ! [D_4447] : D_4447 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_2800,c_2794])).

tff(c_3548,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_3187,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n022.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:09:55 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.62/1.96  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.97  
% 4.62/1.97  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.97  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 4.62/1.97  
% 4.62/1.97  %Foreground sorts:
% 4.62/1.97  
% 4.62/1.97  
% 4.62/1.97  %Background operators:
% 4.62/1.97  
% 4.62/1.97  
% 4.62/1.97  %Foreground operators:
% 4.62/1.97  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.62/1.97  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.62/1.97  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.62/1.97  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.62/1.97  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.62/1.97  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.62/1.97  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.62/1.97  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.62/1.97  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.62/1.97  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.62/1.97  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 4.62/1.97  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.62/1.97  tff('#skF_3', type, '#skF_3': $i).
% 4.62/1.97  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.62/1.97  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.62/1.97  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.62/1.97  tff('#skF_4', type, '#skF_4': $i).
% 4.62/1.97  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.62/1.97  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.62/1.97  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.62/1.97  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.62/1.97  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 4.62/1.97  
% 4.62/1.98  tff(f_77, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 4.62/1.98  tff(f_62, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.62/1.98  tff(f_60, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.62/1.98  tff(f_64, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.62/1.98  tff(f_58, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 4.62/1.98  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.62/1.98  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 4.62/1.98  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 4.62/1.98  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.62/1.98  tff(f_33, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 4.62/1.98  tff(f_39, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.62/1.98  tff(f_54, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.62/1.98  tff(c_56, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.62/1.98  tff(c_44, plain, (![A_27, B_28]: (k1_enumset1(A_27, A_27, B_28)=k2_tarski(A_27, B_28))), inference(cnfTransformation, [status(thm)], [f_62])).
% 4.62/1.98  tff(c_42, plain, (![A_26]: (k2_tarski(A_26, A_26)=k1_tarski(A_26))), inference(cnfTransformation, [status(thm)], [f_60])).
% 4.62/1.98  tff(c_46, plain, (![A_29, B_30, C_31]: (k2_enumset1(A_29, A_29, B_30, C_31)=k1_enumset1(A_29, B_30, C_31))), inference(cnfTransformation, [status(thm)], [f_64])).
% 4.62/1.98  tff(c_558, plain, (![A_103, B_104, C_105, D_106]: (k2_xboole_0(k1_enumset1(A_103, B_104, C_105), k1_tarski(D_106))=k2_enumset1(A_103, B_104, C_105, D_106))), inference(cnfTransformation, [status(thm)], [f_58])).
% 4.62/1.98  tff(c_600, plain, (![A_27, B_28, D_106]: (k2_xboole_0(k2_tarski(A_27, B_28), k1_tarski(D_106))=k2_enumset1(A_27, A_27, B_28, D_106))), inference(superposition, [status(thm), theory('equality')], [c_44, c_558])).
% 4.62/1.98  tff(c_609, plain, (![A_107, B_108, D_109]: (k2_xboole_0(k2_tarski(A_107, B_108), k1_tarski(D_109))=k1_enumset1(A_107, B_108, D_109))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_600])).
% 4.62/1.98  tff(c_639, plain, (![A_26, D_109]: (k2_xboole_0(k1_tarski(A_26), k1_tarski(D_109))=k1_enumset1(A_26, A_26, D_109))), inference(superposition, [status(thm), theory('equality')], [c_42, c_609])).
% 4.62/1.98  tff(c_647, plain, (![A_26, D_109]: (k2_xboole_0(k1_tarski(A_26), k1_tarski(D_109))=k2_tarski(A_26, D_109))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_639])).
% 4.62/1.98  tff(c_648, plain, (![A_110, D_111]: (k2_xboole_0(k1_tarski(A_110), k1_tarski(D_111))=k2_tarski(A_110, D_111))), inference(demodulation, [status(thm), theory('equality')], [c_44, c_639])).
% 4.62/1.98  tff(c_10, plain, (![A_9]: (k5_xboole_0(A_9, k1_xboole_0)=A_9)), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.62/1.98  tff(c_8, plain, (![A_7, B_8]: (k4_xboole_0(A_7, k2_xboole_0(A_7, B_8))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_35])).
% 4.62/1.98  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.62/1.98  tff(c_307, plain, (![A_85, B_86]: (k5_xboole_0(A_85, k3_xboole_0(A_85, B_86))=k4_xboole_0(A_85, B_86))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.62/1.98  tff(c_319, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_307])).
% 4.62/1.98  tff(c_322, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_8, c_319])).
% 4.62/1.98  tff(c_58, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_77])).
% 4.62/1.98  tff(c_125, plain, (![A_76, B_77]: (k3_xboole_0(A_76, B_77)=A_76 | ~r1_tarski(A_76, B_77))), inference(cnfTransformation, [status(thm)], [f_33])).
% 4.62/1.98  tff(c_129, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_58, c_125])).
% 4.62/1.98  tff(c_316, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_129, c_307])).
% 4.62/1.98  tff(c_408, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_322, c_316])).
% 4.62/1.98  tff(c_12, plain, (![A_10, B_11]: (k5_xboole_0(A_10, k4_xboole_0(B_11, A_10))=k2_xboole_0(A_10, B_11))), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.62/1.98  tff(c_412, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_408, c_12])).
% 4.62/1.98  tff(c_415, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_10, c_412])).
% 4.62/1.98  tff(c_663, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_648, c_415])).
% 4.62/1.98  tff(c_608, plain, (![A_27, B_28, D_106]: (k2_xboole_0(k2_tarski(A_27, B_28), k1_tarski(D_106))=k1_enumset1(A_27, B_28, D_106))), inference(demodulation, [status(thm), theory('equality')], [c_46, c_600])).
% 4.62/1.98  tff(c_700, plain, (![D_106]: (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski(D_106))=k1_enumset1('#skF_4', '#skF_3', D_106))), inference(superposition, [status(thm), theory('equality')], [c_663, c_608])).
% 4.62/1.98  tff(c_774, plain, (![D_119]: (k1_enumset1('#skF_4', '#skF_3', D_119)=k2_tarski('#skF_4', D_119))), inference(demodulation, [status(thm), theory('equality')], [c_647, c_700])).
% 4.62/1.98  tff(c_18, plain, (![E_18, A_12, C_14]: (r2_hidden(E_18, k1_enumset1(A_12, E_18, C_14)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.62/1.98  tff(c_800, plain, (![D_119]: (r2_hidden('#skF_3', k2_tarski('#skF_4', D_119)))), inference(superposition, [status(thm), theory('equality')], [c_774, c_18])).
% 4.62/1.98  tff(c_713, plain, (![E_112, C_113, B_114, A_115]: (E_112=C_113 | E_112=B_114 | E_112=A_115 | ~r2_hidden(E_112, k1_enumset1(A_115, B_114, C_113)))), inference(cnfTransformation, [status(thm)], [f_54])).
% 4.62/1.98  tff(c_2768, plain, (![E_218, B_219, A_220]: (E_218=B_219 | E_218=A_220 | E_218=A_220 | ~r2_hidden(E_218, k2_tarski(A_220, B_219)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_713])).
% 4.62/1.98  tff(c_2778, plain, (![D_119]: (D_119='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_800, c_2768])).
% 4.62/1.98  tff(c_2800, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_2778])).
% 4.62/1.98  tff(c_2794, plain, (![D_119]: (D_119='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_2778])).
% 4.62/1.98  tff(c_3187, plain, (![D_4447]: (D_4447='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_2800, c_2794])).
% 4.62/1.98  tff(c_3548, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_3187, c_56])).
% 4.62/1.98  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.62/1.98  
% 4.62/1.98  Inference rules
% 4.62/1.98  ----------------------
% 4.62/1.98  #Ref     : 0
% 4.62/1.98  #Sup     : 998
% 4.62/1.98  #Fact    : 0
% 4.62/1.98  #Define  : 0
% 4.62/1.98  #Split   : 0
% 4.62/1.98  #Chain   : 0
% 4.62/1.98  #Close   : 0
% 4.62/1.98  
% 4.62/1.98  Ordering : KBO
% 4.62/1.98  
% 4.62/1.98  Simplification rules
% 4.62/1.98  ----------------------
% 4.62/1.98  #Subsume      : 139
% 4.62/1.98  #Demod        : 814
% 4.62/1.98  #Tautology    : 588
% 4.62/1.98  #SimpNegUnit  : 9
% 4.62/1.98  #BackRed      : 0
% 4.62/1.98  
% 4.62/1.98  #Partial instantiations: 81
% 4.62/1.98  #Strategies tried      : 1
% 4.62/1.98  
% 4.62/1.98  Timing (in seconds)
% 4.62/1.98  ----------------------
% 4.62/1.98  Preprocessing        : 0.36
% 4.62/1.98  Parsing              : 0.19
% 4.62/1.98  CNF conversion       : 0.03
% 4.62/1.98  Main loop            : 0.72
% 4.62/1.98  Inferencing          : 0.26
% 4.62/1.98  Reduction            : 0.30
% 4.62/1.98  Demodulation         : 0.24
% 4.62/1.98  BG Simplification    : 0.03
% 4.62/1.98  Subsumption          : 0.09
% 4.62/1.98  Abstraction          : 0.03
% 4.62/1.98  MUC search           : 0.00
% 4.62/1.98  Cooper               : 0.00
% 4.62/1.98  Total                : 1.11
% 4.62/1.98  Index Insertion      : 0.00
% 4.62/1.98  Index Deletion       : 0.00
% 4.62/1.98  Index Matching       : 0.00
% 4.62/1.98  BG Taut test         : 0.00
%------------------------------------------------------------------------------

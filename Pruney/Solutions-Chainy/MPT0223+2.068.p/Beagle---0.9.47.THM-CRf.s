%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n016.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:25 EST 2020

% Result     : Theorem 5.36s
% Output     : CNFRefutation 5.36s
% Verified   : 
% Statistics : Number of formulae       :   67 ( 171 expanded)
%              Number of leaves         :   32 (  72 expanded)
%              Depth                    :   14
%              Number of atoms          :   58 ( 187 expanded)
%              Number of equality atoms :   52 ( 174 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(f_75,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_56,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_54,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_58,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_52,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_33,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,k2_xboole_0(A,B)) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,k2_xboole_0(A,B)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t21_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_50,axiom,(
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
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_40,plain,(
    ! [A_22,B_23] : k1_enumset1(A_22,A_22,B_23) = k2_tarski(A_22,B_23) ),
    inference(cnfTransformation,[status(thm)],[f_56])).

tff(c_38,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_54])).

tff(c_42,plain,(
    ! [A_24,B_25,C_26] : k2_enumset1(A_24,A_24,B_25,C_26) = k1_enumset1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_58])).

tff(c_906,plain,(
    ! [A_109,B_110,C_111,D_112] : k2_xboole_0(k1_enumset1(A_109,B_110,C_111),k1_tarski(D_112)) = k2_enumset1(A_109,B_110,C_111,D_112) ),
    inference(cnfTransformation,[status(thm)],[f_52])).

tff(c_960,plain,(
    ! [A_22,B_23,D_112] : k2_xboole_0(k2_tarski(A_22,B_23),k1_tarski(D_112)) = k2_enumset1(A_22,A_22,B_23,D_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_906])).

tff(c_1016,plain,(
    ! [A_117,B_118,D_119] : k2_xboole_0(k2_tarski(A_117,B_118),k1_tarski(D_119)) = k1_enumset1(A_117,B_118,D_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_960])).

tff(c_1040,plain,(
    ! [A_21,D_119] : k2_xboole_0(k1_tarski(A_21),k1_tarski(D_119)) = k1_enumset1(A_21,A_21,D_119) ),
    inference(superposition,[status(thm),theory(equality)],[c_38,c_1016])).

tff(c_1046,plain,(
    ! [A_21,D_119] : k2_xboole_0(k1_tarski(A_21),k1_tarski(D_119)) = k2_tarski(A_21,D_119) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1040])).

tff(c_1056,plain,(
    ! [A_125,D_126] : k2_xboole_0(k1_tarski(A_125),k1_tarski(D_126)) = k2_tarski(A_125,D_126) ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_1040])).

tff(c_8,plain,(
    ! [A_7] : k5_xboole_0(A_7,k1_xboole_0) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_6,plain,(
    ! [A_5,B_6] : k4_xboole_0(A_5,k2_xboole_0(A_5,B_6)) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_4,plain,(
    ! [A_3,B_4] : k3_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_129,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k3_xboole_0(A_77,B_78)) = k4_xboole_0(A_77,B_78) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_141,plain,(
    ! [A_3,B_4] : k4_xboole_0(A_3,k2_xboole_0(A_3,B_4)) = k5_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_129])).

tff(c_144,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_141])).

tff(c_58,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_138,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_58,c_129])).

tff(c_283,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_144,c_138])).

tff(c_445,plain,(
    ! [A_90,B_91] : k5_xboole_0(A_90,k4_xboole_0(B_91,A_90)) = k2_xboole_0(A_90,B_91) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_454,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_283,c_445])).

tff(c_460,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_454])).

tff(c_1074,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(superposition,[status(thm),theory(equality)],[c_1056,c_460])).

tff(c_966,plain,(
    ! [A_22,B_23,D_112] : k2_xboole_0(k2_tarski(A_22,B_23),k1_tarski(D_112)) = k1_enumset1(A_22,B_23,D_112) ),
    inference(demodulation,[status(thm),theory(equality)],[c_42,c_960])).

tff(c_1100,plain,(
    ! [D_112] : k2_xboole_0(k1_tarski('#skF_4'),k1_tarski(D_112)) = k1_enumset1('#skF_4','#skF_3',D_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_1074,c_966])).

tff(c_1143,plain,(
    ! [D_130] : k1_enumset1('#skF_4','#skF_3',D_130) = k2_tarski('#skF_4',D_130) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1046,c_1100])).

tff(c_16,plain,(
    ! [E_16,A_10,C_12] : r2_hidden(E_16,k1_enumset1(A_10,E_16,C_12)) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_1181,plain,(
    ! [D_130] : r2_hidden('#skF_3',k2_tarski('#skF_4',D_130)) ),
    inference(superposition,[status(thm),theory(equality)],[c_1143,c_16])).

tff(c_967,plain,(
    ! [E_113,C_114,B_115,A_116] :
      ( E_113 = C_114
      | E_113 = B_115
      | E_113 = A_116
      | ~ r2_hidden(E_113,k1_enumset1(A_116,B_115,C_114)) ) ),
    inference(cnfTransformation,[status(thm)],[f_50])).

tff(c_3843,plain,(
    ! [E_262,B_263,A_264] :
      ( E_262 = B_263
      | E_262 = A_264
      | E_262 = A_264
      | ~ r2_hidden(E_262,k2_tarski(A_264,B_263)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_967])).

tff(c_3854,plain,(
    ! [D_130] :
      ( D_130 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_1181,c_3843])).

tff(c_3880,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_3854])).

tff(c_3874,plain,(
    ! [D_130] : D_130 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_56,c_56,c_3854])).

tff(c_4283,plain,(
    ! [D_4853] : D_4853 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_3880,c_3874])).

tff(c_4658,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_4283,c_56])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.12/0.34  % Computer   : n016.cluster.edu
% 0.12/0.34  % Model      : x86_64 x86_64
% 0.12/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.12/0.34  % Memory     : 8042.1875MB
% 0.12/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.12/0.34  % CPULimit   : 60
% 0.12/0.34  % DateTime   : Tue Dec  1 17:42:04 EST 2020
% 0.12/0.34  % CPUTime    : 
% 0.12/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.36/1.99  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.36/2.00  
% 5.36/2.00  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.36/2.00  %$ r2_hidden > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.36/2.00  
% 5.36/2.00  %Foreground sorts:
% 5.36/2.00  
% 5.36/2.00  
% 5.36/2.00  %Background operators:
% 5.36/2.00  
% 5.36/2.00  
% 5.36/2.00  %Foreground operators:
% 5.36/2.00  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.36/2.00  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.36/2.00  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.36/2.00  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.36/2.00  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.36/2.00  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.36/2.00  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.36/2.00  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.36/2.00  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.36/2.00  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.36/2.00  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.36/2.00  tff('#skF_3', type, '#skF_3': $i).
% 5.36/2.00  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.36/2.00  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.36/2.00  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.36/2.00  tff('#skF_4', type, '#skF_4': $i).
% 5.36/2.00  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.36/2.00  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.36/2.00  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.36/2.00  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.36/2.00  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.36/2.00  
% 5.36/2.01  tff(f_75, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 5.36/2.01  tff(f_56, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.36/2.01  tff(f_54, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.36/2.01  tff(f_58, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 5.36/2.01  tff(f_52, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 5.36/2.01  tff(f_33, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.36/2.01  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, k2_xboole_0(A, B)) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_xboole_1)).
% 5.36/2.01  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, k2_xboole_0(A, B)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t21_xboole_1)).
% 5.36/2.01  tff(f_27, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.36/2.01  tff(f_35, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.36/2.01  tff(f_50, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.36/2.01  tff(c_56, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.36/2.01  tff(c_40, plain, (![A_22, B_23]: (k1_enumset1(A_22, A_22, B_23)=k2_tarski(A_22, B_23))), inference(cnfTransformation, [status(thm)], [f_56])).
% 5.36/2.01  tff(c_38, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_54])).
% 5.36/2.01  tff(c_42, plain, (![A_24, B_25, C_26]: (k2_enumset1(A_24, A_24, B_25, C_26)=k1_enumset1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_58])).
% 5.36/2.01  tff(c_906, plain, (![A_109, B_110, C_111, D_112]: (k2_xboole_0(k1_enumset1(A_109, B_110, C_111), k1_tarski(D_112))=k2_enumset1(A_109, B_110, C_111, D_112))), inference(cnfTransformation, [status(thm)], [f_52])).
% 5.36/2.01  tff(c_960, plain, (![A_22, B_23, D_112]: (k2_xboole_0(k2_tarski(A_22, B_23), k1_tarski(D_112))=k2_enumset1(A_22, A_22, B_23, D_112))), inference(superposition, [status(thm), theory('equality')], [c_40, c_906])).
% 5.36/2.01  tff(c_1016, plain, (![A_117, B_118, D_119]: (k2_xboole_0(k2_tarski(A_117, B_118), k1_tarski(D_119))=k1_enumset1(A_117, B_118, D_119))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_960])).
% 5.36/2.01  tff(c_1040, plain, (![A_21, D_119]: (k2_xboole_0(k1_tarski(A_21), k1_tarski(D_119))=k1_enumset1(A_21, A_21, D_119))), inference(superposition, [status(thm), theory('equality')], [c_38, c_1016])).
% 5.36/2.01  tff(c_1046, plain, (![A_21, D_119]: (k2_xboole_0(k1_tarski(A_21), k1_tarski(D_119))=k2_tarski(A_21, D_119))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1040])).
% 5.36/2.01  tff(c_1056, plain, (![A_125, D_126]: (k2_xboole_0(k1_tarski(A_125), k1_tarski(D_126))=k2_tarski(A_125, D_126))), inference(demodulation, [status(thm), theory('equality')], [c_40, c_1040])).
% 5.36/2.01  tff(c_8, plain, (![A_7]: (k5_xboole_0(A_7, k1_xboole_0)=A_7)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.36/2.01  tff(c_6, plain, (![A_5, B_6]: (k4_xboole_0(A_5, k2_xboole_0(A_5, B_6))=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.36/2.01  tff(c_4, plain, (![A_3, B_4]: (k3_xboole_0(A_3, k2_xboole_0(A_3, B_4))=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 5.36/2.01  tff(c_129, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k3_xboole_0(A_77, B_78))=k4_xboole_0(A_77, B_78))), inference(cnfTransformation, [status(thm)], [f_27])).
% 5.36/2.01  tff(c_141, plain, (![A_3, B_4]: (k4_xboole_0(A_3, k2_xboole_0(A_3, B_4))=k5_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_129])).
% 5.36/2.01  tff(c_144, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_6, c_141])).
% 5.36/2.01  tff(c_58, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(cnfTransformation, [status(thm)], [f_75])).
% 5.36/2.01  tff(c_138, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_58, c_129])).
% 5.36/2.01  tff(c_283, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_144, c_138])).
% 5.36/2.01  tff(c_445, plain, (![A_90, B_91]: (k5_xboole_0(A_90, k4_xboole_0(B_91, A_90))=k2_xboole_0(A_90, B_91))), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.36/2.01  tff(c_454, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_283, c_445])).
% 5.36/2.01  tff(c_460, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_8, c_454])).
% 5.36/2.01  tff(c_1074, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_1056, c_460])).
% 5.36/2.01  tff(c_966, plain, (![A_22, B_23, D_112]: (k2_xboole_0(k2_tarski(A_22, B_23), k1_tarski(D_112))=k1_enumset1(A_22, B_23, D_112))), inference(demodulation, [status(thm), theory('equality')], [c_42, c_960])).
% 5.36/2.01  tff(c_1100, plain, (![D_112]: (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski(D_112))=k1_enumset1('#skF_4', '#skF_3', D_112))), inference(superposition, [status(thm), theory('equality')], [c_1074, c_966])).
% 5.36/2.01  tff(c_1143, plain, (![D_130]: (k1_enumset1('#skF_4', '#skF_3', D_130)=k2_tarski('#skF_4', D_130))), inference(demodulation, [status(thm), theory('equality')], [c_1046, c_1100])).
% 5.36/2.01  tff(c_16, plain, (![E_16, A_10, C_12]: (r2_hidden(E_16, k1_enumset1(A_10, E_16, C_12)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.36/2.01  tff(c_1181, plain, (![D_130]: (r2_hidden('#skF_3', k2_tarski('#skF_4', D_130)))), inference(superposition, [status(thm), theory('equality')], [c_1143, c_16])).
% 5.36/2.01  tff(c_967, plain, (![E_113, C_114, B_115, A_116]: (E_113=C_114 | E_113=B_115 | E_113=A_116 | ~r2_hidden(E_113, k1_enumset1(A_116, B_115, C_114)))), inference(cnfTransformation, [status(thm)], [f_50])).
% 5.36/2.01  tff(c_3843, plain, (![E_262, B_263, A_264]: (E_262=B_263 | E_262=A_264 | E_262=A_264 | ~r2_hidden(E_262, k2_tarski(A_264, B_263)))), inference(superposition, [status(thm), theory('equality')], [c_40, c_967])).
% 5.36/2.01  tff(c_3854, plain, (![D_130]: (D_130='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_1181, c_3843])).
% 5.36/2.01  tff(c_3880, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_3854])).
% 5.36/2.01  tff(c_3874, plain, (![D_130]: (D_130='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_56, c_56, c_3854])).
% 5.36/2.01  tff(c_4283, plain, (![D_4853]: (D_4853='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_3880, c_3874])).
% 5.36/2.01  tff(c_4658, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_4283, c_56])).
% 5.36/2.01  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.36/2.01  
% 5.36/2.01  Inference rules
% 5.36/2.01  ----------------------
% 5.36/2.01  #Ref     : 0
% 5.36/2.01  #Sup     : 1294
% 5.36/2.01  #Fact    : 1
% 5.36/2.01  #Define  : 0
% 5.36/2.01  #Split   : 0
% 5.36/2.01  #Chain   : 0
% 5.36/2.01  #Close   : 0
% 5.36/2.01  
% 5.36/2.01  Ordering : KBO
% 5.36/2.01  
% 5.36/2.01  Simplification rules
% 5.36/2.01  ----------------------
% 5.36/2.01  #Subsume      : 208
% 5.36/2.01  #Demod        : 892
% 5.36/2.01  #Tautology    : 749
% 5.36/2.01  #SimpNegUnit  : 14
% 5.36/2.01  #BackRed      : 0
% 5.36/2.01  
% 5.36/2.01  #Partial instantiations: 88
% 5.36/2.01  #Strategies tried      : 1
% 5.36/2.01  
% 5.36/2.01  Timing (in seconds)
% 5.36/2.01  ----------------------
% 5.36/2.01  Preprocessing        : 0.33
% 5.36/2.01  Parsing              : 0.17
% 5.36/2.01  CNF conversion       : 0.03
% 5.36/2.01  Main loop            : 0.92
% 5.36/2.01  Inferencing          : 0.31
% 5.36/2.01  Reduction            : 0.38
% 5.36/2.01  Demodulation         : 0.32
% 5.36/2.01  BG Simplification    : 0.03
% 5.36/2.01  Subsumption          : 0.14
% 5.36/2.01  Abstraction          : 0.04
% 5.36/2.01  MUC search           : 0.00
% 5.36/2.01  Cooper               : 0.00
% 5.36/2.01  Total                : 1.28
% 5.36/2.01  Index Insertion      : 0.00
% 5.36/2.01  Index Deletion       : 0.00
% 5.36/2.01  Index Matching       : 0.00
% 5.36/2.01  BG Taut test         : 0.00
%------------------------------------------------------------------------------

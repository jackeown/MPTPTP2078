%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n007.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:47:30 EST 2020

% Result     : Theorem 5.79s
% Output     : CNFRefutation 5.79s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 239 expanded)
%              Number of leaves         :   38 (  98 expanded)
%              Depth                    :   18
%              Number of atoms          :   76 ( 261 expanded)
%              Number of equality atoms :   62 ( 227 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

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

tff(f_89,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k1_tarski(A),k1_tarski(B))
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t6_zfmisc_1)).

tff(f_74,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_72,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_70,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_51,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_49,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : r1_xboole_0(k4_xboole_0(A,B),B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t79_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
    <=> k3_xboole_0(A,B) = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_66,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_68,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_56,plain,(
    ! [A_38,B_39] : k1_enumset1(A_38,A_38,B_39) = k2_tarski(A_38,B_39) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_54,plain,(
    ! [A_37] : k2_tarski(A_37,A_37) = k1_tarski(A_37) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_58,plain,(
    ! [A_40,B_41,C_42] : k2_enumset1(A_40,A_40,B_41,C_42) = k1_enumset1(A_40,B_41,C_42) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_1154,plain,(
    ! [A_148,B_149,C_150,D_151] : k2_xboole_0(k1_enumset1(A_148,B_149,C_150),k1_tarski(D_151)) = k2_enumset1(A_148,B_149,C_150,D_151) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_1193,plain,(
    ! [A_38,B_39,D_151] : k2_xboole_0(k2_tarski(A_38,B_39),k1_tarski(D_151)) = k2_enumset1(A_38,A_38,B_39,D_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1154])).

tff(c_1390,plain,(
    ! [A_155,B_156,D_157] : k2_xboole_0(k2_tarski(A_155,B_156),k1_tarski(D_157)) = k1_enumset1(A_155,B_156,D_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1193])).

tff(c_1417,plain,(
    ! [A_37,D_157] : k2_xboole_0(k1_tarski(A_37),k1_tarski(D_157)) = k1_enumset1(A_37,A_37,D_157) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_1390])).

tff(c_1420,plain,(
    ! [A_37,D_157] : k2_xboole_0(k1_tarski(A_37),k1_tarski(D_157)) = k2_tarski(A_37,D_157) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_1417])).

tff(c_18,plain,(
    ! [A_15] : k5_xboole_0(A_15,k1_xboole_0) = A_15 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_10,plain,(
    ! [A_7] : k3_xboole_0(A_7,A_7) = A_7 ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_232,plain,(
    ! [A_101,B_102] : k5_xboole_0(A_101,k3_xboole_0(A_101,B_102)) = k4_xboole_0(A_101,B_102) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_256,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k4_xboole_0(A_7,A_7) ),
    inference(superposition,[status(thm),theory(equality)],[c_10,c_232])).

tff(c_8,plain,(
    ! [A_5] : k2_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_24,plain,(
    ! [A_21,B_22] : k5_xboole_0(A_21,k4_xboole_0(B_22,A_21)) = k2_xboole_0(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_746,plain,(
    ! [A_131,B_132,C_133] : k5_xboole_0(k5_xboole_0(A_131,B_132),C_133) = k5_xboole_0(A_131,k5_xboole_0(B_132,C_133)) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_2832,plain,(
    ! [A_220,C_221] : k5_xboole_0(k4_xboole_0(A_220,A_220),C_221) = k5_xboole_0(A_220,k5_xboole_0(A_220,C_221)) ),
    inference(superposition,[status(thm),theory(equality)],[c_256,c_746])).

tff(c_2870,plain,(
    ! [A_220] : k5_xboole_0(A_220,k5_xboole_0(A_220,k4_xboole_0(A_220,A_220))) = k4_xboole_0(k4_xboole_0(A_220,A_220),k4_xboole_0(A_220,A_220)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2832,c_256])).

tff(c_3032,plain,(
    ! [A_224] : k4_xboole_0(k4_xboole_0(A_224,A_224),k4_xboole_0(A_224,A_224)) = k4_xboole_0(A_224,A_224) ),
    inference(demodulation,[status(thm),theory(equality)],[c_256,c_8,c_24,c_2870])).

tff(c_20,plain,(
    ! [A_16,B_17] : r1_xboole_0(k4_xboole_0(A_16,B_17),B_17) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_158,plain,(
    ! [A_86,B_87] :
      ( k3_xboole_0(A_86,B_87) = k1_xboole_0
      | ~ r1_xboole_0(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_166,plain,(
    ! [A_16,B_17] : k3_xboole_0(k4_xboole_0(A_16,B_17),B_17) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_20,c_158])).

tff(c_3187,plain,(
    ! [A_227] : k3_xboole_0(k4_xboole_0(A_227,A_227),k4_xboole_0(A_227,A_227)) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3032,c_166])).

tff(c_3198,plain,(
    ! [A_227] : k4_xboole_0(A_227,A_227) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_3187,c_10])).

tff(c_3255,plain,(
    ! [A_7] : k5_xboole_0(A_7,A_7) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3198,c_256])).

tff(c_70,plain,(
    r1_tarski(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_216,plain,(
    ! [A_97,B_98] :
      ( k3_xboole_0(A_97,B_98) = A_97
      | ~ r1_tarski(A_97,B_98) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_220,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_70,c_216])).

tff(c_12,plain,(
    ! [A_9,B_10] : k5_xboole_0(A_9,k3_xboole_0(A_9,B_10)) = k4_xboole_0(A_9,B_10) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_301,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) ),
    inference(superposition,[status(thm),theory(equality)],[c_220,c_12])).

tff(c_3329,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_4')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_3255,c_301])).

tff(c_3428,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),k1_tarski('#skF_3')) = k5_xboole_0(k1_tarski('#skF_4'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_3329,c_24])).

tff(c_3448,plain,(
    k2_tarski('#skF_4','#skF_3') = k1_tarski('#skF_4') ),
    inference(demodulation,[status(thm),theory(equality)],[c_1420,c_18,c_3428])).

tff(c_1196,plain,(
    ! [A_38,B_39,D_151] : k2_xboole_0(k2_tarski(A_38,B_39),k1_tarski(D_151)) = k1_enumset1(A_38,B_39,D_151) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_1193])).

tff(c_3806,plain,(
    ! [D_151] : k2_xboole_0(k1_tarski('#skF_4'),k1_tarski(D_151)) = k1_enumset1('#skF_4','#skF_3',D_151) ),
    inference(superposition,[status(thm),theory(equality)],[c_3448,c_1196])).

tff(c_4263,plain,(
    ! [D_272] : k1_enumset1('#skF_4','#skF_3',D_272) = k2_tarski('#skF_4',D_272) ),
    inference(demodulation,[status(thm),theory(equality)],[c_1420,c_3806])).

tff(c_30,plain,(
    ! [E_29,A_23,C_25] : r2_hidden(E_29,k1_enumset1(A_23,E_29,C_25)) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_4346,plain,(
    ! [D_273] : r2_hidden('#skF_3',k2_tarski('#skF_4',D_273)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4263,c_30])).

tff(c_1421,plain,(
    ! [E_158,C_159,B_160,A_161] :
      ( E_158 = C_159
      | E_158 = B_160
      | E_158 = A_161
      | ~ r2_hidden(E_158,k1_enumset1(A_161,B_160,C_159)) ) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_1436,plain,(
    ! [E_158,B_39,A_38] :
      ( E_158 = B_39
      | E_158 = A_38
      | E_158 = A_38
      | ~ r2_hidden(E_158,k2_tarski(A_38,B_39)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_1421])).

tff(c_4349,plain,(
    ! [D_273] :
      ( D_273 = '#skF_3'
      | '#skF_3' = '#skF_4' ) ),
    inference(resolution,[status(thm)],[c_4346,c_1436])).

tff(c_4410,plain,(
    '#skF_3' = '#skF_4' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_68,c_4349])).

tff(c_4358,plain,(
    ! [D_273] : D_273 = '#skF_3' ),
    inference(negUnitSimplification,[status(thm)],[c_68,c_68,c_4349])).

tff(c_4742,plain,(
    ! [D_4610] : D_4610 = '#skF_4' ),
    inference(superposition,[status(thm),theory(equality)],[c_4410,c_4358])).

tff(c_5054,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_4742,c_68])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.11/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.11/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n007.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 11:05:21 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 5.79/2.16  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.79/2.16  
% 5.79/2.16  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.79/2.17  %$ r2_hidden > r1_xboole_0 > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 5.79/2.17  
% 5.79/2.17  %Foreground sorts:
% 5.79/2.17  
% 5.79/2.17  
% 5.79/2.17  %Background operators:
% 5.79/2.17  
% 5.79/2.17  
% 5.79/2.17  %Foreground operators:
% 5.79/2.17  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 5.79/2.17  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 5.79/2.17  tff(k1_tarski, type, k1_tarski: $i > $i).
% 5.79/2.17  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 5.79/2.17  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 5.79/2.17  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 5.79/2.17  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 5.79/2.17  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 5.79/2.17  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 5.79/2.17  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 5.79/2.17  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 5.79/2.17  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 5.79/2.17  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 5.79/2.17  tff('#skF_3', type, '#skF_3': $i).
% 5.79/2.17  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 5.79/2.17  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 5.79/2.17  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 5.79/2.17  tff('#skF_4', type, '#skF_4': $i).
% 5.79/2.17  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 5.79/2.17  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 5.79/2.17  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 5.79/2.17  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 5.79/2.17  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 5.79/2.17  
% 5.79/2.18  tff(f_89, negated_conjecture, ~(![A, B]: (r1_tarski(k1_tarski(A), k1_tarski(B)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t6_zfmisc_1)).
% 5.79/2.18  tff(f_74, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 5.79/2.18  tff(f_72, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 5.79/2.18  tff(f_76, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 5.79/2.18  tff(f_70, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 5.79/2.18  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 5.79/2.18  tff(f_35, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 5.79/2.18  tff(f_37, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 5.79/2.18  tff(f_33, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 5.79/2.18  tff(f_51, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 5.79/2.18  tff(f_49, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 5.79/2.18  tff(f_47, axiom, (![A, B]: r1_xboole_0(k4_xboole_0(A, B), B)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t79_xboole_1)).
% 5.79/2.18  tff(f_31, axiom, (![A, B]: (r1_xboole_0(A, B) <=> (k3_xboole_0(A, B) = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d7_xboole_0)).
% 5.79/2.18  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 5.79/2.18  tff(f_66, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 5.79/2.18  tff(c_68, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.79/2.18  tff(c_56, plain, (![A_38, B_39]: (k1_enumset1(A_38, A_38, B_39)=k2_tarski(A_38, B_39))), inference(cnfTransformation, [status(thm)], [f_74])).
% 5.79/2.18  tff(c_54, plain, (![A_37]: (k2_tarski(A_37, A_37)=k1_tarski(A_37))), inference(cnfTransformation, [status(thm)], [f_72])).
% 5.79/2.18  tff(c_58, plain, (![A_40, B_41, C_42]: (k2_enumset1(A_40, A_40, B_41, C_42)=k1_enumset1(A_40, B_41, C_42))), inference(cnfTransformation, [status(thm)], [f_76])).
% 5.79/2.18  tff(c_1154, plain, (![A_148, B_149, C_150, D_151]: (k2_xboole_0(k1_enumset1(A_148, B_149, C_150), k1_tarski(D_151))=k2_enumset1(A_148, B_149, C_150, D_151))), inference(cnfTransformation, [status(thm)], [f_70])).
% 5.79/2.18  tff(c_1193, plain, (![A_38, B_39, D_151]: (k2_xboole_0(k2_tarski(A_38, B_39), k1_tarski(D_151))=k2_enumset1(A_38, A_38, B_39, D_151))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1154])).
% 5.79/2.18  tff(c_1390, plain, (![A_155, B_156, D_157]: (k2_xboole_0(k2_tarski(A_155, B_156), k1_tarski(D_157))=k1_enumset1(A_155, B_156, D_157))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1193])).
% 5.79/2.18  tff(c_1417, plain, (![A_37, D_157]: (k2_xboole_0(k1_tarski(A_37), k1_tarski(D_157))=k1_enumset1(A_37, A_37, D_157))), inference(superposition, [status(thm), theory('equality')], [c_54, c_1390])).
% 5.79/2.18  tff(c_1420, plain, (![A_37, D_157]: (k2_xboole_0(k1_tarski(A_37), k1_tarski(D_157))=k2_tarski(A_37, D_157))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_1417])).
% 5.79/2.18  tff(c_18, plain, (![A_15]: (k5_xboole_0(A_15, k1_xboole_0)=A_15)), inference(cnfTransformation, [status(thm)], [f_45])).
% 5.79/2.18  tff(c_10, plain, (![A_7]: (k3_xboole_0(A_7, A_7)=A_7)), inference(cnfTransformation, [status(thm)], [f_35])).
% 5.79/2.18  tff(c_232, plain, (![A_101, B_102]: (k5_xboole_0(A_101, k3_xboole_0(A_101, B_102))=k4_xboole_0(A_101, B_102))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.79/2.18  tff(c_256, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k4_xboole_0(A_7, A_7))), inference(superposition, [status(thm), theory('equality')], [c_10, c_232])).
% 5.79/2.18  tff(c_8, plain, (![A_5]: (k2_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_33])).
% 5.79/2.18  tff(c_24, plain, (![A_21, B_22]: (k5_xboole_0(A_21, k4_xboole_0(B_22, A_21))=k2_xboole_0(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_51])).
% 5.79/2.18  tff(c_746, plain, (![A_131, B_132, C_133]: (k5_xboole_0(k5_xboole_0(A_131, B_132), C_133)=k5_xboole_0(A_131, k5_xboole_0(B_132, C_133)))), inference(cnfTransformation, [status(thm)], [f_49])).
% 5.79/2.18  tff(c_2832, plain, (![A_220, C_221]: (k5_xboole_0(k4_xboole_0(A_220, A_220), C_221)=k5_xboole_0(A_220, k5_xboole_0(A_220, C_221)))), inference(superposition, [status(thm), theory('equality')], [c_256, c_746])).
% 5.79/2.18  tff(c_2870, plain, (![A_220]: (k5_xboole_0(A_220, k5_xboole_0(A_220, k4_xboole_0(A_220, A_220)))=k4_xboole_0(k4_xboole_0(A_220, A_220), k4_xboole_0(A_220, A_220)))), inference(superposition, [status(thm), theory('equality')], [c_2832, c_256])).
% 5.79/2.18  tff(c_3032, plain, (![A_224]: (k4_xboole_0(k4_xboole_0(A_224, A_224), k4_xboole_0(A_224, A_224))=k4_xboole_0(A_224, A_224))), inference(demodulation, [status(thm), theory('equality')], [c_256, c_8, c_24, c_2870])).
% 5.79/2.18  tff(c_20, plain, (![A_16, B_17]: (r1_xboole_0(k4_xboole_0(A_16, B_17), B_17))), inference(cnfTransformation, [status(thm)], [f_47])).
% 5.79/2.18  tff(c_158, plain, (![A_86, B_87]: (k3_xboole_0(A_86, B_87)=k1_xboole_0 | ~r1_xboole_0(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_31])).
% 5.79/2.18  tff(c_166, plain, (![A_16, B_17]: (k3_xboole_0(k4_xboole_0(A_16, B_17), B_17)=k1_xboole_0)), inference(resolution, [status(thm)], [c_20, c_158])).
% 5.79/2.18  tff(c_3187, plain, (![A_227]: (k3_xboole_0(k4_xboole_0(A_227, A_227), k4_xboole_0(A_227, A_227))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3032, c_166])).
% 5.79/2.18  tff(c_3198, plain, (![A_227]: (k4_xboole_0(A_227, A_227)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3187, c_10])).
% 5.79/2.18  tff(c_3255, plain, (![A_7]: (k5_xboole_0(A_7, A_7)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_3198, c_256])).
% 5.79/2.18  tff(c_70, plain, (r1_tarski(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(cnfTransformation, [status(thm)], [f_89])).
% 5.79/2.18  tff(c_216, plain, (![A_97, B_98]: (k3_xboole_0(A_97, B_98)=A_97 | ~r1_tarski(A_97, B_98))), inference(cnfTransformation, [status(thm)], [f_43])).
% 5.79/2.18  tff(c_220, plain, (k3_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_70, c_216])).
% 5.79/2.18  tff(c_12, plain, (![A_9, B_10]: (k5_xboole_0(A_9, k3_xboole_0(A_9, B_10))=k4_xboole_0(A_9, B_10))), inference(cnfTransformation, [status(thm)], [f_37])).
% 5.79/2.18  tff(c_301, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))), inference(superposition, [status(thm), theory('equality')], [c_220, c_12])).
% 5.79/2.18  tff(c_3329, plain, (k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_4'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_3255, c_301])).
% 5.79/2.18  tff(c_3428, plain, (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski('#skF_3'))=k5_xboole_0(k1_tarski('#skF_4'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_3329, c_24])).
% 5.79/2.18  tff(c_3448, plain, (k2_tarski('#skF_4', '#skF_3')=k1_tarski('#skF_4')), inference(demodulation, [status(thm), theory('equality')], [c_1420, c_18, c_3428])).
% 5.79/2.18  tff(c_1196, plain, (![A_38, B_39, D_151]: (k2_xboole_0(k2_tarski(A_38, B_39), k1_tarski(D_151))=k1_enumset1(A_38, B_39, D_151))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_1193])).
% 5.79/2.18  tff(c_3806, plain, (![D_151]: (k2_xboole_0(k1_tarski('#skF_4'), k1_tarski(D_151))=k1_enumset1('#skF_4', '#skF_3', D_151))), inference(superposition, [status(thm), theory('equality')], [c_3448, c_1196])).
% 5.79/2.18  tff(c_4263, plain, (![D_272]: (k1_enumset1('#skF_4', '#skF_3', D_272)=k2_tarski('#skF_4', D_272))), inference(demodulation, [status(thm), theory('equality')], [c_1420, c_3806])).
% 5.79/2.18  tff(c_30, plain, (![E_29, A_23, C_25]: (r2_hidden(E_29, k1_enumset1(A_23, E_29, C_25)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.79/2.18  tff(c_4346, plain, (![D_273]: (r2_hidden('#skF_3', k2_tarski('#skF_4', D_273)))), inference(superposition, [status(thm), theory('equality')], [c_4263, c_30])).
% 5.79/2.18  tff(c_1421, plain, (![E_158, C_159, B_160, A_161]: (E_158=C_159 | E_158=B_160 | E_158=A_161 | ~r2_hidden(E_158, k1_enumset1(A_161, B_160, C_159)))), inference(cnfTransformation, [status(thm)], [f_66])).
% 5.79/2.18  tff(c_1436, plain, (![E_158, B_39, A_38]: (E_158=B_39 | E_158=A_38 | E_158=A_38 | ~r2_hidden(E_158, k2_tarski(A_38, B_39)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_1421])).
% 5.79/2.18  tff(c_4349, plain, (![D_273]: (D_273='#skF_3' | '#skF_3'='#skF_4')), inference(resolution, [status(thm)], [c_4346, c_1436])).
% 5.79/2.18  tff(c_4410, plain, ('#skF_3'='#skF_4'), inference(negUnitSimplification, [status(thm)], [c_68, c_68, c_4349])).
% 5.79/2.18  tff(c_4358, plain, (![D_273]: (D_273='#skF_3')), inference(negUnitSimplification, [status(thm)], [c_68, c_68, c_4349])).
% 5.79/2.18  tff(c_4742, plain, (![D_4610]: (D_4610='#skF_4')), inference(superposition, [status(thm), theory('equality')], [c_4410, c_4358])).
% 5.79/2.18  tff(c_5054, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_4742, c_68])).
% 5.79/2.18  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 5.79/2.18  
% 5.79/2.18  Inference rules
% 5.79/2.18  ----------------------
% 5.79/2.18  #Ref     : 0
% 5.79/2.18  #Sup     : 1330
% 5.79/2.18  #Fact    : 0
% 5.79/2.18  #Define  : 0
% 5.79/2.18  #Split   : 0
% 5.79/2.18  #Chain   : 0
% 5.79/2.18  #Close   : 0
% 5.79/2.18  
% 5.79/2.18  Ordering : KBO
% 5.79/2.18  
% 5.79/2.18  Simplification rules
% 5.79/2.18  ----------------------
% 5.79/2.18  #Subsume      : 115
% 5.79/2.18  #Demod        : 1007
% 5.79/2.18  #Tautology    : 792
% 5.79/2.18  #SimpNegUnit  : 1
% 5.79/2.18  #BackRed      : 35
% 5.79/2.18  
% 5.79/2.18  #Partial instantiations: 83
% 5.79/2.18  #Strategies tried      : 1
% 5.79/2.18  
% 5.79/2.18  Timing (in seconds)
% 5.79/2.18  ----------------------
% 5.79/2.18  Preprocessing        : 0.35
% 5.79/2.18  Parsing              : 0.18
% 5.79/2.18  CNF conversion       : 0.03
% 5.79/2.18  Main loop            : 1.05
% 5.79/2.19  Inferencing          : 0.37
% 5.79/2.19  Reduction            : 0.43
% 5.79/2.19  Demodulation         : 0.34
% 5.79/2.19  BG Simplification    : 0.04
% 5.79/2.19  Subsumption          : 0.15
% 5.79/2.19  Abstraction          : 0.05
% 5.79/2.19  MUC search           : 0.00
% 5.79/2.19  Cooper               : 0.00
% 5.79/2.19  Total                : 1.44
% 5.79/2.19  Index Insertion      : 0.00
% 5.79/2.19  Index Deletion       : 0.00
% 5.79/2.19  Index Matching       : 0.00
% 5.79/2.19  BG Taut test         : 0.00
%------------------------------------------------------------------------------

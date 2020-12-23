%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n009.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:53:06 EST 2020

% Result     : Theorem 13.04s
% Output     : CNFRefutation 13.04s
% Verified   : 
% Statistics : Number of formulae       :   80 ( 194 expanded)
%              Number of leaves         :   35 (  79 expanded)
%              Depth                    :   12
%              Number of atoms          :   73 ( 188 expanded)
%              Number of equality atoms :   55 ( 170 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(r1_xboole_0,type,(
    r1_xboole_0: ( $i * $i ) > $o )).

tff('#skF_2',type,(
    '#skF_2': $i )).

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

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_35,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_45,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_39,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_74,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l31_zfmisc_1)).

tff(f_51,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_76,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_70,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_29,axiom,(
    ! [A,B] : k2_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k2_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t88_xboole_1)).

tff(c_18,plain,(
    ! [A_18] : k5_xboole_0(A_18,A_18) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_838,plain,(
    ! [A_103,B_104] : k5_xboole_0(k5_xboole_0(A_103,B_104),k2_xboole_0(A_103,B_104)) = k3_xboole_0(A_103,B_104) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_16,plain,(
    ! [A_15,B_16,C_17] : k5_xboole_0(k5_xboole_0(A_15,B_16),C_17) = k5_xboole_0(A_15,k5_xboole_0(B_16,C_17)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_4235,plain,(
    ! [A_183,B_184] : k5_xboole_0(A_183,k5_xboole_0(B_184,k2_xboole_0(A_183,B_184))) = k3_xboole_0(A_183,B_184) ),
    inference(superposition,[status(thm),theory(equality)],[c_838,c_16])).

tff(c_125,plain,(
    ! [B_65,A_66] : k5_xboole_0(B_65,A_66) = k5_xboole_0(A_66,B_65) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_12,plain,(
    ! [A_12] : k5_xboole_0(A_12,k1_xboole_0) = A_12 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_141,plain,(
    ! [A_66] : k5_xboole_0(k1_xboole_0,A_66) = A_66 ),
    inference(superposition,[status(thm),theory(equality)],[c_125,c_12])).

tff(c_405,plain,(
    ! [A_92,B_93,C_94] : k5_xboole_0(k5_xboole_0(A_92,B_93),C_94) = k5_xboole_0(A_92,k5_xboole_0(B_93,C_94)) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_469,plain,(
    ! [A_18,C_94] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_94)) = k5_xboole_0(k1_xboole_0,C_94) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_405])).

tff(c_482,plain,(
    ! [A_18,C_94] : k5_xboole_0(A_18,k5_xboole_0(A_18,C_94)) = C_94 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_469])).

tff(c_4282,plain,(
    ! [B_184,A_183] : k5_xboole_0(B_184,k2_xboole_0(A_183,B_184)) = k5_xboole_0(A_183,k3_xboole_0(A_183,B_184)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4235,c_482])).

tff(c_4395,plain,(
    ! [B_185,A_186] : k5_xboole_0(B_185,k2_xboole_0(A_186,B_185)) = k4_xboole_0(A_186,B_185) ),
    inference(demodulation,[status(thm),theory(equality)],[c_8,c_4282])).

tff(c_4451,plain,(
    ! [B_185,A_186] : k5_xboole_0(B_185,k4_xboole_0(A_186,B_185)) = k2_xboole_0(A_186,B_185) ),
    inference(superposition,[status(thm),theory(equality)],[c_4395,c_482])).

tff(c_384,plain,(
    ! [B_87,A_88] :
      ( k3_xboole_0(B_87,k1_tarski(A_88)) = k1_tarski(A_88)
      | ~ r2_hidden(A_88,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_10736,plain,(
    ! [B_253,A_254] :
      ( k5_xboole_0(B_253,k1_tarski(A_254)) = k4_xboole_0(B_253,k1_tarski(A_254))
      | ~ r2_hidden(A_254,B_253) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_384,c_8])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_483,plain,(
    ! [A_95,C_96] : k5_xboole_0(A_95,k5_xboole_0(A_95,C_96)) = C_96 ),
    inference(demodulation,[status(thm),theory(equality)],[c_141,c_469])).

tff(c_526,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_483])).

tff(c_10842,plain,(
    ! [A_254,B_253] :
      ( k5_xboole_0(k1_tarski(A_254),k4_xboole_0(B_253,k1_tarski(A_254))) = B_253
      | ~ r2_hidden(A_254,B_253) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10736,c_526])).

tff(c_10983,plain,(
    ! [B_255,A_256] :
      ( k2_xboole_0(B_255,k1_tarski(A_256)) = B_255
      | ~ r2_hidden(A_256,B_255) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4451,c_10842])).

tff(c_22,plain,(
    ! [B_22,A_21] : k2_tarski(B_22,A_21) = k2_tarski(A_21,B_22) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_226,plain,(
    ! [A_70,B_71] : k3_tarski(k2_tarski(A_70,B_71)) = k2_xboole_0(A_70,B_71) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_267,plain,(
    ! [A_77,B_78] : k3_tarski(k2_tarski(A_77,B_78)) = k2_xboole_0(B_78,A_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_226])).

tff(c_42,plain,(
    ! [A_55,B_56] : k3_tarski(k2_tarski(A_55,B_56)) = k2_xboole_0(A_55,B_56) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_273,plain,(
    ! [B_78,A_77] : k2_xboole_0(B_78,A_77) = k2_xboole_0(A_77,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_42])).

tff(c_4499,plain,(
    ! [B_78,A_77] : k5_xboole_0(B_78,k2_xboole_0(B_78,A_77)) = k4_xboole_0(A_77,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_4395])).

tff(c_11044,plain,(
    ! [B_255,A_256] :
      ( k5_xboole_0(B_255,B_255) = k4_xboole_0(k1_tarski(A_256),B_255)
      | ~ r2_hidden(A_256,B_255) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_10983,c_4499])).

tff(c_11687,plain,(
    ! [A_262,B_263] :
      ( k4_xboole_0(k1_tarski(A_262),B_263) = k1_xboole_0
      | ~ r2_hidden(A_262,B_263) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_11044])).

tff(c_46,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_11801,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11687,c_46])).

tff(c_38,plain,(
    ! [A_51,B_52] :
      ( r1_xboole_0(k1_tarski(A_51),B_52)
      | r2_hidden(A_51,B_52) ) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_4,plain,(
    ! [A_3] : k2_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_977,plain,(
    ! [A_107,B_108,C_109] : k2_xboole_0(k2_xboole_0(A_107,B_108),C_109) = k2_xboole_0(A_107,k2_xboole_0(B_108,C_109)) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_1056,plain,(
    ! [A_116,C_117] : k2_xboole_0(A_116,k2_xboole_0(A_116,C_117)) = k2_xboole_0(A_116,C_117) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_977])).

tff(c_1091,plain,(
    ! [A_77,B_78] : k2_xboole_0(A_77,k2_xboole_0(B_78,A_77)) = k2_xboole_0(A_77,B_78) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_1056])).

tff(c_4902,plain,(
    ! [B_192,A_193] : k5_xboole_0(B_192,k2_xboole_0(B_192,A_193)) = k4_xboole_0(A_193,B_192) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_4395])).

tff(c_4987,plain,(
    ! [A_77,B_78] : k5_xboole_0(A_77,k2_xboole_0(A_77,B_78)) = k4_xboole_0(k2_xboole_0(B_78,A_77),A_77) ),
    inference(superposition,[status(thm),theory(equality)],[c_1091,c_4902])).

tff(c_5038,plain,(
    ! [B_78,A_77] : k4_xboole_0(k2_xboole_0(B_78,A_77),A_77) = k4_xboole_0(B_78,A_77) ),
    inference(demodulation,[status(thm),theory(equality)],[c_4499,c_4987])).

tff(c_14,plain,(
    ! [A_13,B_14] :
      ( k4_xboole_0(k2_xboole_0(A_13,B_14),B_14) = A_13
      | ~ r1_xboole_0(A_13,B_14) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_12402,plain,(
    ! [A_269,B_270] :
      ( k4_xboole_0(A_269,B_270) = A_269
      | ~ r1_xboole_0(A_269,B_270) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5038,c_14])).

tff(c_27317,plain,(
    ! [A_366,B_367] :
      ( k4_xboole_0(k1_tarski(A_366),B_367) = k1_tarski(A_366)
      | r2_hidden(A_366,B_367) ) ),
    inference(resolution,[status(thm)],[c_38,c_12402])).

tff(c_44,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_27405,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_27317,c_44])).

tff(c_27462,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11801,c_27405])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.06/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.06/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n009.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 17:34:26 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 13.04/6.12  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.04/6.12  
% 13.04/6.12  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.04/6.13  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 13.04/6.13  
% 13.04/6.13  %Foreground sorts:
% 13.04/6.13  
% 13.04/6.13  
% 13.04/6.13  %Background operators:
% 13.04/6.13  
% 13.04/6.13  
% 13.04/6.13  %Foreground operators:
% 13.04/6.13  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 13.04/6.13  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 13.04/6.13  tff(k1_tarski, type, k1_tarski: $i > $i).
% 13.04/6.13  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 13.04/6.13  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 13.04/6.13  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 13.04/6.13  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 13.04/6.13  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 13.04/6.13  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 13.04/6.13  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 13.04/6.13  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 13.04/6.13  tff('#skF_2', type, '#skF_2': $i).
% 13.04/6.13  tff('#skF_1', type, '#skF_1': $i).
% 13.04/6.13  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 13.04/6.13  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 13.04/6.13  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 13.04/6.13  tff(k3_tarski, type, k3_tarski: $i > $i).
% 13.04/6.13  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 13.04/6.13  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 13.04/6.13  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 13.04/6.13  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 13.04/6.13  
% 13.04/6.14  tff(f_47, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t92_xboole_1)).
% 13.04/6.14  tff(f_35, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 13.04/6.14  tff(f_49, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t95_xboole_1)).
% 13.04/6.14  tff(f_45, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 13.04/6.14  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 13.04/6.14  tff(f_39, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 13.04/6.14  tff(f_74, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l31_zfmisc_1)).
% 13.04/6.14  tff(f_51, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 13.04/6.14  tff(f_76, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 13.04/6.14  tff(f_81, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 13.04/6.14  tff(f_70, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 13.04/6.14  tff(f_29, axiom, (![A, B]: (k2_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k2_xboole_0)).
% 13.04/6.14  tff(f_37, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t4_xboole_1)).
% 13.04/6.14  tff(f_43, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t88_xboole_1)).
% 13.04/6.14  tff(c_18, plain, (![A_18]: (k5_xboole_0(A_18, A_18)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_47])).
% 13.04/6.14  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_35])).
% 13.04/6.14  tff(c_838, plain, (![A_103, B_104]: (k5_xboole_0(k5_xboole_0(A_103, B_104), k2_xboole_0(A_103, B_104))=k3_xboole_0(A_103, B_104))), inference(cnfTransformation, [status(thm)], [f_49])).
% 13.04/6.14  tff(c_16, plain, (![A_15, B_16, C_17]: (k5_xboole_0(k5_xboole_0(A_15, B_16), C_17)=k5_xboole_0(A_15, k5_xboole_0(B_16, C_17)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.04/6.14  tff(c_4235, plain, (![A_183, B_184]: (k5_xboole_0(A_183, k5_xboole_0(B_184, k2_xboole_0(A_183, B_184)))=k3_xboole_0(A_183, B_184))), inference(superposition, [status(thm), theory('equality')], [c_838, c_16])).
% 13.04/6.14  tff(c_125, plain, (![B_65, A_66]: (k5_xboole_0(B_65, A_66)=k5_xboole_0(A_66, B_65))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.04/6.14  tff(c_12, plain, (![A_12]: (k5_xboole_0(A_12, k1_xboole_0)=A_12)), inference(cnfTransformation, [status(thm)], [f_39])).
% 13.04/6.14  tff(c_141, plain, (![A_66]: (k5_xboole_0(k1_xboole_0, A_66)=A_66)), inference(superposition, [status(thm), theory('equality')], [c_125, c_12])).
% 13.04/6.14  tff(c_405, plain, (![A_92, B_93, C_94]: (k5_xboole_0(k5_xboole_0(A_92, B_93), C_94)=k5_xboole_0(A_92, k5_xboole_0(B_93, C_94)))), inference(cnfTransformation, [status(thm)], [f_45])).
% 13.04/6.14  tff(c_469, plain, (![A_18, C_94]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_94))=k5_xboole_0(k1_xboole_0, C_94))), inference(superposition, [status(thm), theory('equality')], [c_18, c_405])).
% 13.04/6.14  tff(c_482, plain, (![A_18, C_94]: (k5_xboole_0(A_18, k5_xboole_0(A_18, C_94))=C_94)), inference(demodulation, [status(thm), theory('equality')], [c_141, c_469])).
% 13.04/6.14  tff(c_4282, plain, (![B_184, A_183]: (k5_xboole_0(B_184, k2_xboole_0(A_183, B_184))=k5_xboole_0(A_183, k3_xboole_0(A_183, B_184)))), inference(superposition, [status(thm), theory('equality')], [c_4235, c_482])).
% 13.04/6.14  tff(c_4395, plain, (![B_185, A_186]: (k5_xboole_0(B_185, k2_xboole_0(A_186, B_185))=k4_xboole_0(A_186, B_185))), inference(demodulation, [status(thm), theory('equality')], [c_8, c_4282])).
% 13.04/6.14  tff(c_4451, plain, (![B_185, A_186]: (k5_xboole_0(B_185, k4_xboole_0(A_186, B_185))=k2_xboole_0(A_186, B_185))), inference(superposition, [status(thm), theory('equality')], [c_4395, c_482])).
% 13.04/6.14  tff(c_384, plain, (![B_87, A_88]: (k3_xboole_0(B_87, k1_tarski(A_88))=k1_tarski(A_88) | ~r2_hidden(A_88, B_87))), inference(cnfTransformation, [status(thm)], [f_74])).
% 13.04/6.14  tff(c_10736, plain, (![B_253, A_254]: (k5_xboole_0(B_253, k1_tarski(A_254))=k4_xboole_0(B_253, k1_tarski(A_254)) | ~r2_hidden(A_254, B_253))), inference(superposition, [status(thm), theory('equality')], [c_384, c_8])).
% 13.04/6.14  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 13.04/6.14  tff(c_483, plain, (![A_95, C_96]: (k5_xboole_0(A_95, k5_xboole_0(A_95, C_96))=C_96)), inference(demodulation, [status(thm), theory('equality')], [c_141, c_469])).
% 13.04/6.14  tff(c_526, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_483])).
% 13.04/6.14  tff(c_10842, plain, (![A_254, B_253]: (k5_xboole_0(k1_tarski(A_254), k4_xboole_0(B_253, k1_tarski(A_254)))=B_253 | ~r2_hidden(A_254, B_253))), inference(superposition, [status(thm), theory('equality')], [c_10736, c_526])).
% 13.04/6.14  tff(c_10983, plain, (![B_255, A_256]: (k2_xboole_0(B_255, k1_tarski(A_256))=B_255 | ~r2_hidden(A_256, B_255))), inference(demodulation, [status(thm), theory('equality')], [c_4451, c_10842])).
% 13.04/6.14  tff(c_22, plain, (![B_22, A_21]: (k2_tarski(B_22, A_21)=k2_tarski(A_21, B_22))), inference(cnfTransformation, [status(thm)], [f_51])).
% 13.04/6.14  tff(c_226, plain, (![A_70, B_71]: (k3_tarski(k2_tarski(A_70, B_71))=k2_xboole_0(A_70, B_71))), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.04/6.14  tff(c_267, plain, (![A_77, B_78]: (k3_tarski(k2_tarski(A_77, B_78))=k2_xboole_0(B_78, A_77))), inference(superposition, [status(thm), theory('equality')], [c_22, c_226])).
% 13.04/6.14  tff(c_42, plain, (![A_55, B_56]: (k3_tarski(k2_tarski(A_55, B_56))=k2_xboole_0(A_55, B_56))), inference(cnfTransformation, [status(thm)], [f_76])).
% 13.04/6.14  tff(c_273, plain, (![B_78, A_77]: (k2_xboole_0(B_78, A_77)=k2_xboole_0(A_77, B_78))), inference(superposition, [status(thm), theory('equality')], [c_267, c_42])).
% 13.04/6.14  tff(c_4499, plain, (![B_78, A_77]: (k5_xboole_0(B_78, k2_xboole_0(B_78, A_77))=k4_xboole_0(A_77, B_78))), inference(superposition, [status(thm), theory('equality')], [c_273, c_4395])).
% 13.04/6.14  tff(c_11044, plain, (![B_255, A_256]: (k5_xboole_0(B_255, B_255)=k4_xboole_0(k1_tarski(A_256), B_255) | ~r2_hidden(A_256, B_255))), inference(superposition, [status(thm), theory('equality')], [c_10983, c_4499])).
% 13.04/6.14  tff(c_11687, plain, (![A_262, B_263]: (k4_xboole_0(k1_tarski(A_262), B_263)=k1_xboole_0 | ~r2_hidden(A_262, B_263))), inference(demodulation, [status(thm), theory('equality')], [c_18, c_11044])).
% 13.04/6.14  tff(c_46, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.04/6.14  tff(c_11801, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11687, c_46])).
% 13.04/6.14  tff(c_38, plain, (![A_51, B_52]: (r1_xboole_0(k1_tarski(A_51), B_52) | r2_hidden(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_70])).
% 13.04/6.14  tff(c_4, plain, (![A_3]: (k2_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 13.04/6.14  tff(c_977, plain, (![A_107, B_108, C_109]: (k2_xboole_0(k2_xboole_0(A_107, B_108), C_109)=k2_xboole_0(A_107, k2_xboole_0(B_108, C_109)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 13.04/6.14  tff(c_1056, plain, (![A_116, C_117]: (k2_xboole_0(A_116, k2_xboole_0(A_116, C_117))=k2_xboole_0(A_116, C_117))), inference(superposition, [status(thm), theory('equality')], [c_4, c_977])).
% 13.04/6.14  tff(c_1091, plain, (![A_77, B_78]: (k2_xboole_0(A_77, k2_xboole_0(B_78, A_77))=k2_xboole_0(A_77, B_78))), inference(superposition, [status(thm), theory('equality')], [c_273, c_1056])).
% 13.04/6.14  tff(c_4902, plain, (![B_192, A_193]: (k5_xboole_0(B_192, k2_xboole_0(B_192, A_193))=k4_xboole_0(A_193, B_192))), inference(superposition, [status(thm), theory('equality')], [c_273, c_4395])).
% 13.04/6.14  tff(c_4987, plain, (![A_77, B_78]: (k5_xboole_0(A_77, k2_xboole_0(A_77, B_78))=k4_xboole_0(k2_xboole_0(B_78, A_77), A_77))), inference(superposition, [status(thm), theory('equality')], [c_1091, c_4902])).
% 13.04/6.14  tff(c_5038, plain, (![B_78, A_77]: (k4_xboole_0(k2_xboole_0(B_78, A_77), A_77)=k4_xboole_0(B_78, A_77))), inference(demodulation, [status(thm), theory('equality')], [c_4499, c_4987])).
% 13.04/6.14  tff(c_14, plain, (![A_13, B_14]: (k4_xboole_0(k2_xboole_0(A_13, B_14), B_14)=A_13 | ~r1_xboole_0(A_13, B_14))), inference(cnfTransformation, [status(thm)], [f_43])).
% 13.04/6.14  tff(c_12402, plain, (![A_269, B_270]: (k4_xboole_0(A_269, B_270)=A_269 | ~r1_xboole_0(A_269, B_270))), inference(demodulation, [status(thm), theory('equality')], [c_5038, c_14])).
% 13.04/6.14  tff(c_27317, plain, (![A_366, B_367]: (k4_xboole_0(k1_tarski(A_366), B_367)=k1_tarski(A_366) | r2_hidden(A_366, B_367))), inference(resolution, [status(thm)], [c_38, c_12402])).
% 13.04/6.14  tff(c_44, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 13.04/6.14  tff(c_27405, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_27317, c_44])).
% 13.04/6.14  tff(c_27462, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11801, c_27405])).
% 13.04/6.14  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 13.04/6.14  
% 13.04/6.14  Inference rules
% 13.04/6.14  ----------------------
% 13.04/6.14  #Ref     : 0
% 13.04/6.14  #Sup     : 6792
% 13.04/6.14  #Fact    : 0
% 13.04/6.14  #Define  : 0
% 13.04/6.14  #Split   : 0
% 13.04/6.14  #Chain   : 0
% 13.04/6.14  #Close   : 0
% 13.04/6.14  
% 13.04/6.14  Ordering : KBO
% 13.04/6.14  
% 13.04/6.14  Simplification rules
% 13.04/6.14  ----------------------
% 13.04/6.14  #Subsume      : 661
% 13.04/6.14  #Demod        : 9204
% 13.04/6.14  #Tautology    : 2980
% 13.04/6.14  #SimpNegUnit  : 1
% 13.04/6.14  #BackRed      : 3
% 13.04/6.14  
% 13.04/6.14  #Partial instantiations: 0
% 13.04/6.14  #Strategies tried      : 1
% 13.04/6.14  
% 13.04/6.14  Timing (in seconds)
% 13.04/6.14  ----------------------
% 13.04/6.15  Preprocessing        : 0.34
% 13.04/6.15  Parsing              : 0.18
% 13.04/6.15  CNF conversion       : 0.02
% 13.04/6.15  Main loop            : 5.04
% 13.04/6.15  Inferencing          : 0.80
% 13.04/6.15  Reduction            : 3.27
% 13.04/6.15  Demodulation         : 3.03
% 13.04/6.15  BG Simplification    : 0.13
% 13.04/6.15  Subsumption          : 0.65
% 13.04/6.15  Abstraction          : 0.20
% 13.04/6.15  MUC search           : 0.00
% 13.04/6.15  Cooper               : 0.00
% 13.04/6.15  Total                : 5.42
% 13.04/6.15  Index Insertion      : 0.00
% 13.04/6.15  Index Deletion       : 0.00
% 13.04/6.15  Index Matching       : 0.00
% 13.04/6.15  BG Taut test         : 0.00
%------------------------------------------------------------------------------

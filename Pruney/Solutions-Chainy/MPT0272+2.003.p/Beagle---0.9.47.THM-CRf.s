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
% DateTime   : Thu Dec  3 09:53:06 EST 2020

% Result     : Theorem 14.14s
% Output     : CNFRefutation 14.23s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 200 expanded)
%              Number of leaves         :   36 (  81 expanded)
%              Depth                    :   12
%              Number of atoms          :   77 ( 195 expanded)
%              Number of equality atoms :   58 ( 176 expanded)
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

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,A) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t92_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k5_xboole_0(k5_xboole_0(A,B),k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t95_xboole_1)).

tff(f_43,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k5_xboole_0(A,B) = k5_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k5_xboole_0)).

tff(f_37,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_76,axiom,(
    ! [A,B] :
      ( r2_hidden(A,B)
     => k3_xboole_0(B,k1_tarski(A)) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t52_zfmisc_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_tarski(A,B) = k2_tarski(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_tarski)).

tff(f_70,axiom,(
    ! [A,B] : k3_tarski(k2_tarski(A,B)) = k2_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l51_zfmisc_1)).

tff(f_81,negated_conjecture,(
    ~ ! [A,B] :
        ( k4_xboole_0(k1_tarski(A),B) = k1_xboole_0
        | k4_xboole_0(k1_tarski(A),B) = k1_tarski(A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_zfmisc_1)).

tff(f_68,axiom,(
    ! [A,B] :
      ( ~ r2_hidden(A,B)
     => r1_xboole_0(k1_tarski(A),B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l27_zfmisc_1)).

tff(f_72,axiom,(
    ! [A] : k3_tarski(k1_tarski(A)) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t31_zfmisc_1)).

tff(f_51,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_35,axiom,(
    ! [A,B,C] : k2_xboole_0(k2_xboole_0(A,B),C) = k2_xboole_0(A,k2_xboole_0(B,C)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_xboole_0(A,B)
     => k4_xboole_0(k2_xboole_0(A,B),B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t88_xboole_1)).

tff(c_16,plain,(
    ! [A_16] : k5_xboole_0(A_16,A_16) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_6,plain,(
    ! [A_5,B_6] : k5_xboole_0(A_5,k3_xboole_0(A_5,B_6)) = k4_xboole_0(A_5,B_6) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_18,plain,(
    ! [A_17,B_18] : k5_xboole_0(k5_xboole_0(A_17,B_18),k2_xboole_0(A_17,B_18)) = k3_xboole_0(A_17,B_18) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_718,plain,(
    ! [A_104,B_105,C_106] : k5_xboole_0(k5_xboole_0(A_104,B_105),C_106) = k5_xboole_0(A_104,k5_xboole_0(B_105,C_106)) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_2024,plain,(
    ! [A_155,B_156] : k5_xboole_0(A_155,k5_xboole_0(B_156,k2_xboole_0(A_155,B_156))) = k3_xboole_0(A_155,B_156) ),
    inference(superposition,[status(thm),theory(equality)],[c_18,c_718])).

tff(c_124,plain,(
    ! [B_62,A_63] : k5_xboole_0(B_62,A_63) = k5_xboole_0(A_63,B_62) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_10,plain,(
    ! [A_10] : k5_xboole_0(A_10,k1_xboole_0) = A_10 ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_140,plain,(
    ! [A_63] : k5_xboole_0(k1_xboole_0,A_63) = A_63 ),
    inference(superposition,[status(thm),theory(equality)],[c_124,c_10])).

tff(c_795,plain,(
    ! [A_16,C_106] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_106)) = k5_xboole_0(k1_xboole_0,C_106) ),
    inference(superposition,[status(thm),theory(equality)],[c_16,c_718])).

tff(c_808,plain,(
    ! [A_16,C_106] : k5_xboole_0(A_16,k5_xboole_0(A_16,C_106)) = C_106 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_795])).

tff(c_2046,plain,(
    ! [B_156,A_155] : k5_xboole_0(B_156,k2_xboole_0(A_155,B_156)) = k5_xboole_0(A_155,k3_xboole_0(A_155,B_156)) ),
    inference(superposition,[status(thm),theory(equality)],[c_2024,c_808])).

tff(c_2443,plain,(
    ! [B_167,A_168] : k5_xboole_0(B_167,k2_xboole_0(A_168,B_167)) = k4_xboole_0(A_168,B_167) ),
    inference(demodulation,[status(thm),theory(equality)],[c_6,c_2046])).

tff(c_2473,plain,(
    ! [B_167,A_168] : k5_xboole_0(B_167,k4_xboole_0(A_168,B_167)) = k2_xboole_0(A_168,B_167) ),
    inference(superposition,[status(thm),theory(equality)],[c_2443,c_808])).

tff(c_364,plain,(
    ! [B_86,A_87] :
      ( k3_xboole_0(B_86,k1_tarski(A_87)) = k1_tarski(A_87)
      | ~ r2_hidden(A_87,B_86) ) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_11000,plain,(
    ! [B_260,A_261] :
      ( k5_xboole_0(B_260,k1_tarski(A_261)) = k4_xboole_0(B_260,k1_tarski(A_261))
      | ~ r2_hidden(A_261,B_260) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_364,c_6])).

tff(c_2,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,A_1) = k5_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_820,plain,(
    ! [A_108,C_109] : k5_xboole_0(A_108,k5_xboole_0(A_108,C_109)) = C_109 ),
    inference(demodulation,[status(thm),theory(equality)],[c_140,c_795])).

tff(c_869,plain,(
    ! [A_1,B_2] : k5_xboole_0(A_1,k5_xboole_0(B_2,A_1)) = B_2 ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_820])).

tff(c_11107,plain,(
    ! [A_261,B_260] :
      ( k5_xboole_0(k1_tarski(A_261),k4_xboole_0(B_260,k1_tarski(A_261))) = B_260
      | ~ r2_hidden(A_261,B_260) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11000,c_869])).

tff(c_11257,plain,(
    ! [B_262,A_263] :
      ( k2_xboole_0(B_262,k1_tarski(A_263)) = B_262
      | ~ r2_hidden(A_263,B_262) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2473,c_11107])).

tff(c_20,plain,(
    ! [B_20,A_19] : k2_tarski(B_20,A_19) = k2_tarski(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_222,plain,(
    ! [A_67,B_68] : k3_tarski(k2_tarski(A_67,B_68)) = k2_xboole_0(A_67,B_68) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_267,plain,(
    ! [B_76,A_77] : k3_tarski(k2_tarski(B_76,A_77)) = k2_xboole_0(A_77,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_20,c_222])).

tff(c_38,plain,(
    ! [A_51,B_52] : k3_tarski(k2_tarski(A_51,B_52)) = k2_xboole_0(A_51,B_52) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_273,plain,(
    ! [B_76,A_77] : k2_xboole_0(B_76,A_77) = k2_xboole_0(A_77,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_267,c_38])).

tff(c_2517,plain,(
    ! [B_76,A_77] : k5_xboole_0(B_76,k2_xboole_0(B_76,A_77)) = k4_xboole_0(A_77,B_76) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_2443])).

tff(c_11306,plain,(
    ! [B_262,A_263] :
      ( k5_xboole_0(B_262,B_262) = k4_xboole_0(k1_tarski(A_263),B_262)
      | ~ r2_hidden(A_263,B_262) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_11257,c_2517])).

tff(c_11422,plain,(
    ! [A_264,B_265] :
      ( k4_xboole_0(k1_tarski(A_264),B_265) = k1_xboole_0
      | ~ r2_hidden(A_264,B_265) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_11306])).

tff(c_46,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_11532,plain,(
    ~ r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_11422,c_46])).

tff(c_36,plain,(
    ! [A_49,B_50] :
      ( r1_xboole_0(k1_tarski(A_49),B_50)
      | r2_hidden(A_49,B_50) ) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_40,plain,(
    ! [A_53] : k3_tarski(k1_tarski(A_53)) = A_53 ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_22,plain,(
    ! [A_21] : k2_tarski(A_21,A_21) = k1_tarski(A_21) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_237,plain,(
    ! [A_21] : k3_tarski(k1_tarski(A_21)) = k2_xboole_0(A_21,A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_222])).

tff(c_240,plain,(
    ! [A_21] : k2_xboole_0(A_21,A_21) = A_21 ),
    inference(demodulation,[status(thm),theory(equality)],[c_40,c_237])).

tff(c_405,plain,(
    ! [A_91,B_92,C_93] : k2_xboole_0(k2_xboole_0(A_91,B_92),C_93) = k2_xboole_0(A_91,k2_xboole_0(B_92,C_93)) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_447,plain,(
    ! [A_21,C_93] : k2_xboole_0(A_21,k2_xboole_0(A_21,C_93)) = k2_xboole_0(A_21,C_93) ),
    inference(superposition,[status(thm),theory(equality)],[c_240,c_405])).

tff(c_5645,plain,(
    ! [B_204,A_205] : k5_xboole_0(B_204,k2_xboole_0(B_204,A_205)) = k4_xboole_0(A_205,B_204) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_2443])).

tff(c_5754,plain,(
    ! [A_21,C_93] : k5_xboole_0(A_21,k2_xboole_0(A_21,C_93)) = k4_xboole_0(k2_xboole_0(A_21,C_93),A_21) ),
    inference(superposition,[status(thm),theory(equality)],[c_447,c_5645])).

tff(c_5789,plain,(
    ! [A_21,C_93] : k4_xboole_0(k2_xboole_0(A_21,C_93),A_21) = k4_xboole_0(C_93,A_21) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2517,c_5754])).

tff(c_376,plain,(
    ! [A_88,B_89] :
      ( k4_xboole_0(k2_xboole_0(A_88,B_89),B_89) = A_88
      | ~ r1_xboole_0(A_88,B_89) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_388,plain,(
    ! [A_77,B_76] :
      ( k4_xboole_0(k2_xboole_0(A_77,B_76),A_77) = B_76
      | ~ r1_xboole_0(B_76,A_77) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_273,c_376])).

tff(c_10989,plain,(
    ! [B_258,A_259] :
      ( k4_xboole_0(B_258,A_259) = B_258
      | ~ r1_xboole_0(B_258,A_259) ) ),
    inference(demodulation,[status(thm),theory(equality)],[c_5789,c_388])).

tff(c_35805,plain,(
    ! [A_400,B_401] :
      ( k4_xboole_0(k1_tarski(A_400),B_401) = k1_tarski(A_400)
      | r2_hidden(A_400,B_401) ) ),
    inference(resolution,[status(thm)],[c_36,c_10989])).

tff(c_44,plain,(
    k4_xboole_0(k1_tarski('#skF_1'),'#skF_2') != k1_tarski('#skF_1') ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_35897,plain,(
    r2_hidden('#skF_1','#skF_2') ),
    inference(superposition,[status(thm),theory(equality)],[c_35805,c_44])).

tff(c_35958,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_11532,c_35897])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.04/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.04/0.14  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.35  % Computer   : n022.cluster.edu
% 0.14/0.35  % Model      : x86_64 x86_64
% 0.14/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.35  % Memory     : 8042.1875MB
% 0.14/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.35  % CPULimit   : 60
% 0.14/0.35  % DateTime   : Tue Dec  1 11:00:41 EST 2020
% 0.14/0.35  % CPUTime    : 
% 0.14/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 14.14/7.50  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.14/7.51  
% 14.14/7.51  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.14/7.51  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_2 > #skF_1
% 14.14/7.51  
% 14.14/7.51  %Foreground sorts:
% 14.14/7.51  
% 14.14/7.51  
% 14.14/7.51  %Background operators:
% 14.14/7.51  
% 14.14/7.51  
% 14.14/7.51  %Foreground operators:
% 14.14/7.51  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 14.14/7.51  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 14.14/7.51  tff(k1_tarski, type, k1_tarski: $i > $i).
% 14.14/7.51  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 14.14/7.51  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 14.14/7.51  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 14.14/7.51  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 14.14/7.51  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 14.14/7.51  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 14.14/7.51  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 14.14/7.51  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 14.14/7.51  tff('#skF_2', type, '#skF_2': $i).
% 14.14/7.51  tff('#skF_1', type, '#skF_1': $i).
% 14.14/7.51  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 14.14/7.51  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 14.14/7.51  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 14.14/7.51  tff(k3_tarski, type, k3_tarski: $i > $i).
% 14.14/7.51  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 14.14/7.51  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 14.14/7.51  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 14.14/7.51  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 14.14/7.51  
% 14.23/7.53  tff(f_45, axiom, (![A]: (k5_xboole_0(A, A) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t92_xboole_1)).
% 14.23/7.53  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 14.23/7.53  tff(f_47, axiom, (![A, B]: (k3_xboole_0(A, B) = k5_xboole_0(k5_xboole_0(A, B), k2_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t95_xboole_1)).
% 14.23/7.53  tff(f_43, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t91_xboole_1)).
% 14.23/7.53  tff(f_27, axiom, (![A, B]: (k5_xboole_0(A, B) = k5_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k5_xboole_0)).
% 14.23/7.53  tff(f_37, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 14.23/7.53  tff(f_76, axiom, (![A, B]: (r2_hidden(A, B) => (k3_xboole_0(B, k1_tarski(A)) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t52_zfmisc_1)).
% 14.23/7.53  tff(f_49, axiom, (![A, B]: (k2_tarski(A, B) = k2_tarski(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_tarski)).
% 14.23/7.53  tff(f_70, axiom, (![A, B]: (k3_tarski(k2_tarski(A, B)) = k2_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l51_zfmisc_1)).
% 14.23/7.53  tff(f_81, negated_conjecture, ~(![A, B]: ((k4_xboole_0(k1_tarski(A), B) = k1_xboole_0) | (k4_xboole_0(k1_tarski(A), B) = k1_tarski(A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_zfmisc_1)).
% 14.23/7.53  tff(f_68, axiom, (![A, B]: (~r2_hidden(A, B) => r1_xboole_0(k1_tarski(A), B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l27_zfmisc_1)).
% 14.23/7.53  tff(f_72, axiom, (![A]: (k3_tarski(k1_tarski(A)) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t31_zfmisc_1)).
% 14.23/7.53  tff(f_51, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 14.23/7.53  tff(f_35, axiom, (![A, B, C]: (k2_xboole_0(k2_xboole_0(A, B), C) = k2_xboole_0(A, k2_xboole_0(B, C)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_1)).
% 14.23/7.53  tff(f_41, axiom, (![A, B]: (r1_xboole_0(A, B) => (k4_xboole_0(k2_xboole_0(A, B), B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t88_xboole_1)).
% 14.23/7.53  tff(c_16, plain, (![A_16]: (k5_xboole_0(A_16, A_16)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_45])).
% 14.23/7.53  tff(c_6, plain, (![A_5, B_6]: (k5_xboole_0(A_5, k3_xboole_0(A_5, B_6))=k4_xboole_0(A_5, B_6))), inference(cnfTransformation, [status(thm)], [f_33])).
% 14.23/7.53  tff(c_18, plain, (![A_17, B_18]: (k5_xboole_0(k5_xboole_0(A_17, B_18), k2_xboole_0(A_17, B_18))=k3_xboole_0(A_17, B_18))), inference(cnfTransformation, [status(thm)], [f_47])).
% 14.23/7.53  tff(c_718, plain, (![A_104, B_105, C_106]: (k5_xboole_0(k5_xboole_0(A_104, B_105), C_106)=k5_xboole_0(A_104, k5_xboole_0(B_105, C_106)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 14.23/7.53  tff(c_2024, plain, (![A_155, B_156]: (k5_xboole_0(A_155, k5_xboole_0(B_156, k2_xboole_0(A_155, B_156)))=k3_xboole_0(A_155, B_156))), inference(superposition, [status(thm), theory('equality')], [c_18, c_718])).
% 14.23/7.53  tff(c_124, plain, (![B_62, A_63]: (k5_xboole_0(B_62, A_63)=k5_xboole_0(A_63, B_62))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.23/7.53  tff(c_10, plain, (![A_10]: (k5_xboole_0(A_10, k1_xboole_0)=A_10)), inference(cnfTransformation, [status(thm)], [f_37])).
% 14.23/7.53  tff(c_140, plain, (![A_63]: (k5_xboole_0(k1_xboole_0, A_63)=A_63)), inference(superposition, [status(thm), theory('equality')], [c_124, c_10])).
% 14.23/7.53  tff(c_795, plain, (![A_16, C_106]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_106))=k5_xboole_0(k1_xboole_0, C_106))), inference(superposition, [status(thm), theory('equality')], [c_16, c_718])).
% 14.23/7.53  tff(c_808, plain, (![A_16, C_106]: (k5_xboole_0(A_16, k5_xboole_0(A_16, C_106))=C_106)), inference(demodulation, [status(thm), theory('equality')], [c_140, c_795])).
% 14.23/7.53  tff(c_2046, plain, (![B_156, A_155]: (k5_xboole_0(B_156, k2_xboole_0(A_155, B_156))=k5_xboole_0(A_155, k3_xboole_0(A_155, B_156)))), inference(superposition, [status(thm), theory('equality')], [c_2024, c_808])).
% 14.23/7.53  tff(c_2443, plain, (![B_167, A_168]: (k5_xboole_0(B_167, k2_xboole_0(A_168, B_167))=k4_xboole_0(A_168, B_167))), inference(demodulation, [status(thm), theory('equality')], [c_6, c_2046])).
% 14.23/7.53  tff(c_2473, plain, (![B_167, A_168]: (k5_xboole_0(B_167, k4_xboole_0(A_168, B_167))=k2_xboole_0(A_168, B_167))), inference(superposition, [status(thm), theory('equality')], [c_2443, c_808])).
% 14.23/7.53  tff(c_364, plain, (![B_86, A_87]: (k3_xboole_0(B_86, k1_tarski(A_87))=k1_tarski(A_87) | ~r2_hidden(A_87, B_86))), inference(cnfTransformation, [status(thm)], [f_76])).
% 14.23/7.53  tff(c_11000, plain, (![B_260, A_261]: (k5_xboole_0(B_260, k1_tarski(A_261))=k4_xboole_0(B_260, k1_tarski(A_261)) | ~r2_hidden(A_261, B_260))), inference(superposition, [status(thm), theory('equality')], [c_364, c_6])).
% 14.23/7.53  tff(c_2, plain, (![B_2, A_1]: (k5_xboole_0(B_2, A_1)=k5_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 14.23/7.53  tff(c_820, plain, (![A_108, C_109]: (k5_xboole_0(A_108, k5_xboole_0(A_108, C_109))=C_109)), inference(demodulation, [status(thm), theory('equality')], [c_140, c_795])).
% 14.23/7.53  tff(c_869, plain, (![A_1, B_2]: (k5_xboole_0(A_1, k5_xboole_0(B_2, A_1))=B_2)), inference(superposition, [status(thm), theory('equality')], [c_2, c_820])).
% 14.23/7.53  tff(c_11107, plain, (![A_261, B_260]: (k5_xboole_0(k1_tarski(A_261), k4_xboole_0(B_260, k1_tarski(A_261)))=B_260 | ~r2_hidden(A_261, B_260))), inference(superposition, [status(thm), theory('equality')], [c_11000, c_869])).
% 14.23/7.53  tff(c_11257, plain, (![B_262, A_263]: (k2_xboole_0(B_262, k1_tarski(A_263))=B_262 | ~r2_hidden(A_263, B_262))), inference(demodulation, [status(thm), theory('equality')], [c_2473, c_11107])).
% 14.23/7.53  tff(c_20, plain, (![B_20, A_19]: (k2_tarski(B_20, A_19)=k2_tarski(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_49])).
% 14.23/7.53  tff(c_222, plain, (![A_67, B_68]: (k3_tarski(k2_tarski(A_67, B_68))=k2_xboole_0(A_67, B_68))), inference(cnfTransformation, [status(thm)], [f_70])).
% 14.23/7.53  tff(c_267, plain, (![B_76, A_77]: (k3_tarski(k2_tarski(B_76, A_77))=k2_xboole_0(A_77, B_76))), inference(superposition, [status(thm), theory('equality')], [c_20, c_222])).
% 14.23/7.53  tff(c_38, plain, (![A_51, B_52]: (k3_tarski(k2_tarski(A_51, B_52))=k2_xboole_0(A_51, B_52))), inference(cnfTransformation, [status(thm)], [f_70])).
% 14.23/7.53  tff(c_273, plain, (![B_76, A_77]: (k2_xboole_0(B_76, A_77)=k2_xboole_0(A_77, B_76))), inference(superposition, [status(thm), theory('equality')], [c_267, c_38])).
% 14.23/7.53  tff(c_2517, plain, (![B_76, A_77]: (k5_xboole_0(B_76, k2_xboole_0(B_76, A_77))=k4_xboole_0(A_77, B_76))), inference(superposition, [status(thm), theory('equality')], [c_273, c_2443])).
% 14.23/7.53  tff(c_11306, plain, (![B_262, A_263]: (k5_xboole_0(B_262, B_262)=k4_xboole_0(k1_tarski(A_263), B_262) | ~r2_hidden(A_263, B_262))), inference(superposition, [status(thm), theory('equality')], [c_11257, c_2517])).
% 14.23/7.53  tff(c_11422, plain, (![A_264, B_265]: (k4_xboole_0(k1_tarski(A_264), B_265)=k1_xboole_0 | ~r2_hidden(A_264, B_265))), inference(demodulation, [status(thm), theory('equality')], [c_16, c_11306])).
% 14.23/7.53  tff(c_46, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_xboole_0), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.23/7.53  tff(c_11532, plain, (~r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_11422, c_46])).
% 14.23/7.53  tff(c_36, plain, (![A_49, B_50]: (r1_xboole_0(k1_tarski(A_49), B_50) | r2_hidden(A_49, B_50))), inference(cnfTransformation, [status(thm)], [f_68])).
% 14.23/7.53  tff(c_40, plain, (![A_53]: (k3_tarski(k1_tarski(A_53))=A_53)), inference(cnfTransformation, [status(thm)], [f_72])).
% 14.23/7.53  tff(c_22, plain, (![A_21]: (k2_tarski(A_21, A_21)=k1_tarski(A_21))), inference(cnfTransformation, [status(thm)], [f_51])).
% 14.23/7.53  tff(c_237, plain, (![A_21]: (k3_tarski(k1_tarski(A_21))=k2_xboole_0(A_21, A_21))), inference(superposition, [status(thm), theory('equality')], [c_22, c_222])).
% 14.23/7.53  tff(c_240, plain, (![A_21]: (k2_xboole_0(A_21, A_21)=A_21)), inference(demodulation, [status(thm), theory('equality')], [c_40, c_237])).
% 14.23/7.53  tff(c_405, plain, (![A_91, B_92, C_93]: (k2_xboole_0(k2_xboole_0(A_91, B_92), C_93)=k2_xboole_0(A_91, k2_xboole_0(B_92, C_93)))), inference(cnfTransformation, [status(thm)], [f_35])).
% 14.23/7.53  tff(c_447, plain, (![A_21, C_93]: (k2_xboole_0(A_21, k2_xboole_0(A_21, C_93))=k2_xboole_0(A_21, C_93))), inference(superposition, [status(thm), theory('equality')], [c_240, c_405])).
% 14.23/7.53  tff(c_5645, plain, (![B_204, A_205]: (k5_xboole_0(B_204, k2_xboole_0(B_204, A_205))=k4_xboole_0(A_205, B_204))), inference(superposition, [status(thm), theory('equality')], [c_273, c_2443])).
% 14.23/7.53  tff(c_5754, plain, (![A_21, C_93]: (k5_xboole_0(A_21, k2_xboole_0(A_21, C_93))=k4_xboole_0(k2_xboole_0(A_21, C_93), A_21))), inference(superposition, [status(thm), theory('equality')], [c_447, c_5645])).
% 14.23/7.53  tff(c_5789, plain, (![A_21, C_93]: (k4_xboole_0(k2_xboole_0(A_21, C_93), A_21)=k4_xboole_0(C_93, A_21))), inference(demodulation, [status(thm), theory('equality')], [c_2517, c_5754])).
% 14.23/7.53  tff(c_376, plain, (![A_88, B_89]: (k4_xboole_0(k2_xboole_0(A_88, B_89), B_89)=A_88 | ~r1_xboole_0(A_88, B_89))), inference(cnfTransformation, [status(thm)], [f_41])).
% 14.23/7.53  tff(c_388, plain, (![A_77, B_76]: (k4_xboole_0(k2_xboole_0(A_77, B_76), A_77)=B_76 | ~r1_xboole_0(B_76, A_77))), inference(superposition, [status(thm), theory('equality')], [c_273, c_376])).
% 14.23/7.53  tff(c_10989, plain, (![B_258, A_259]: (k4_xboole_0(B_258, A_259)=B_258 | ~r1_xboole_0(B_258, A_259))), inference(demodulation, [status(thm), theory('equality')], [c_5789, c_388])).
% 14.23/7.53  tff(c_35805, plain, (![A_400, B_401]: (k4_xboole_0(k1_tarski(A_400), B_401)=k1_tarski(A_400) | r2_hidden(A_400, B_401))), inference(resolution, [status(thm)], [c_36, c_10989])).
% 14.23/7.53  tff(c_44, plain, (k4_xboole_0(k1_tarski('#skF_1'), '#skF_2')!=k1_tarski('#skF_1')), inference(cnfTransformation, [status(thm)], [f_81])).
% 14.23/7.53  tff(c_35897, plain, (r2_hidden('#skF_1', '#skF_2')), inference(superposition, [status(thm), theory('equality')], [c_35805, c_44])).
% 14.23/7.53  tff(c_35958, plain, $false, inference(negUnitSimplification, [status(thm)], [c_11532, c_35897])).
% 14.23/7.53  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 14.23/7.53  
% 14.23/7.53  Inference rules
% 14.23/7.53  ----------------------
% 14.23/7.53  #Ref     : 0
% 14.23/7.53  #Sup     : 9019
% 14.23/7.53  #Fact    : 0
% 14.23/7.53  #Define  : 0
% 14.23/7.53  #Split   : 0
% 14.23/7.53  #Chain   : 0
% 14.23/7.53  #Close   : 0
% 14.23/7.53  
% 14.23/7.53  Ordering : KBO
% 14.23/7.53  
% 14.23/7.53  Simplification rules
% 14.23/7.53  ----------------------
% 14.23/7.53  #Subsume      : 771
% 14.23/7.53  #Demod        : 12278
% 14.23/7.53  #Tautology    : 3872
% 14.23/7.53  #SimpNegUnit  : 1
% 14.23/7.53  #BackRed      : 4
% 14.23/7.53  
% 14.23/7.53  #Partial instantiations: 0
% 14.23/7.53  #Strategies tried      : 1
% 14.23/7.53  
% 14.23/7.53  Timing (in seconds)
% 14.23/7.53  ----------------------
% 14.23/7.53  Preprocessing        : 0.33
% 14.23/7.53  Parsing              : 0.19
% 14.23/7.53  CNF conversion       : 0.02
% 14.23/7.53  Main loop            : 6.34
% 14.23/7.53  Inferencing          : 0.87
% 14.23/7.53  Reduction            : 4.32
% 14.23/7.53  Demodulation         : 4.04
% 14.23/7.53  BG Simplification    : 0.14
% 14.23/7.53  Subsumption          : 0.77
% 14.23/7.53  Abstraction          : 0.23
% 14.23/7.53  MUC search           : 0.00
% 14.23/7.53  Cooper               : 0.00
% 14.23/7.53  Total                : 6.71
% 14.23/7.53  Index Insertion      : 0.00
% 14.23/7.53  Index Deletion       : 0.00
% 14.23/7.53  Index Matching       : 0.00
% 14.23/7.53  BG Taut test         : 0.00
%------------------------------------------------------------------------------

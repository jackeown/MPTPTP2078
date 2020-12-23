%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n025.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:50:39 EST 2020

% Result     : Theorem 4.16s
% Output     : CNFRefutation 4.16s
% Verified   : 
% Statistics : Number of formulae       :   89 ( 542 expanded)
%              Number of leaves         :   37 ( 197 expanded)
%              Depth                    :   16
%              Number of atoms          :   84 ( 843 expanded)
%              Number of equality atoms :   49 ( 455 expanded)
%              Maximal formula depth    :   10 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_1',type,(
    '#skF_1': ( $i * $i * $i ) > $i )).

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

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff(k3_tarski,type,(
    k3_tarski: $i > $i )).

tff('#skF_4',type,(
    '#skF_4': $i )).

tff('#skF_3',type,(
    '#skF_3': $i > $i )).

tff('#nlpp_002',type,(
    '#nlpp': ( $int * $int ) > $int )).

tff(k3_xboole_0,type,(
    k3_xboole_0: ( $i * $i ) > $i )).

tff(k2_xboole_0,type,(
    k2_xboole_0: ( $i * $i ) > $i )).

tff(k5_enumset1,type,(
    k5_enumset1: ( $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff(f_90,negated_conjecture,(
    ~ ! [A,B] :
        ( r1_tarski(k2_xboole_0(k1_tarski(A),B),B)
       => r2_hidden(A,B) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t45_zfmisc_1)).

tff(f_59,axiom,(
    ! [A,B] : r1_tarski(A,k2_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_1)).

tff(f_63,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_57,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t5_boole)).

tff(f_47,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( C = k4_xboole_0(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( r2_hidden(D,A)
            & ~ r2_hidden(D,B) ) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d5_xboole_0)).

tff(f_39,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_61,axiom,(
    ! [A,B,C] : k5_xboole_0(k5_xboole_0(A,B),C) = k5_xboole_0(A,k5_xboole_0(B,C)) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t91_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_53,axiom,(
    ! [A,B] :
      ( A = B
    <=> ( r1_tarski(A,B)
        & r1_tarski(B,A) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',d10_xboole_0)).

tff(f_65,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_85,axiom,(
    ! [A,B,C] :
      ( r1_tarski(k2_tarski(A,B),C)
    <=> ( r2_hidden(A,C)
        & r2_hidden(B,C) ) ) ),
    file('/export/starexec/sandbox2/benchmark/theBenchmark.p',t38_zfmisc_1)).

tff(c_64,plain,(
    ~ r2_hidden('#skF_4','#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_36,plain,(
    ! [A_18,B_19] : r1_tarski(A_18,k2_xboole_0(A_18,B_19)) ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_40,plain,(
    ! [A_23,B_24] : k5_xboole_0(A_23,k4_xboole_0(B_24,A_23)) = k2_xboole_0(A_23,B_24) ),
    inference(cnfTransformation,[status(thm)],[f_63])).

tff(c_34,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_24,plain,(
    ! [A_11] :
      ( r2_hidden('#skF_3'(A_11),A_11)
      | k1_xboole_0 = A_11 ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_177,plain,(
    ! [D_73,A_74,B_75] :
      ( r2_hidden(D_73,A_74)
      | ~ r2_hidden(D_73,k4_xboole_0(A_74,B_75)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_615,plain,(
    ! [A_135,B_136] :
      ( r2_hidden('#skF_3'(k4_xboole_0(A_135,B_136)),A_135)
      | k4_xboole_0(A_135,B_136) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_177])).

tff(c_351,plain,(
    ! [D_104,B_105,A_106] :
      ( ~ r2_hidden(D_104,B_105)
      | ~ r2_hidden(D_104,k4_xboole_0(A_106,B_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_359,plain,(
    ! [A_106,B_105] :
      ( ~ r2_hidden('#skF_3'(k4_xboole_0(A_106,B_105)),B_105)
      | k4_xboole_0(A_106,B_105) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_24,c_351])).

tff(c_634,plain,(
    ! [A_135] : k4_xboole_0(A_135,A_135) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_615,c_359])).

tff(c_22,plain,(
    ! [A_9] : k3_xboole_0(A_9,A_9) = A_9 ),
    inference(cnfTransformation,[status(thm)],[f_39])).

tff(c_202,plain,(
    ! [A_79,B_80] : k5_xboole_0(A_79,k3_xboole_0(A_79,B_80)) = k4_xboole_0(A_79,B_80) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_217,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k4_xboole_0(A_9,A_9) ),
    inference(superposition,[status(thm),theory(equality)],[c_22,c_202])).

tff(c_640,plain,(
    ! [A_9] : k5_xboole_0(A_9,A_9) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_217])).

tff(c_666,plain,(
    ! [A_138] : k5_xboole_0(A_138,A_138) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_634,c_217])).

tff(c_38,plain,(
    ! [A_20,B_21,C_22] : k5_xboole_0(k5_xboole_0(A_20,B_21),C_22) = k5_xboole_0(A_20,k5_xboole_0(B_21,C_22)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1015,plain,(
    ! [A_170,C_171] : k5_xboole_0(A_170,k5_xboole_0(A_170,C_171)) = k5_xboole_0(k1_xboole_0,C_171) ),
    inference(superposition,[status(thm),theory(equality)],[c_666,c_38])).

tff(c_1052,plain,(
    ! [A_9] : k5_xboole_0(k1_xboole_0,A_9) = k5_xboole_0(A_9,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_640,c_1015])).

tff(c_1089,plain,(
    ! [A_9] : k5_xboole_0(k1_xboole_0,A_9) = A_9 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1052])).

tff(c_679,plain,(
    ! [A_138,C_22] : k5_xboole_0(A_138,k5_xboole_0(A_138,C_22)) = k5_xboole_0(k1_xboole_0,C_22) ),
    inference(superposition,[status(thm),theory(equality)],[c_666,c_38])).

tff(c_1433,plain,(
    ! [A_195,C_196] : k5_xboole_0(A_195,k5_xboole_0(A_195,C_196)) = C_196 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_679])).

tff(c_2101,plain,(
    ! [A_217,B_218] : k5_xboole_0(A_217,k2_xboole_0(A_217,B_218)) = k4_xboole_0(B_218,A_217) ),
    inference(superposition,[status(thm),theory(equality)],[c_40,c_1433])).

tff(c_1527,plain,(
    ! [A_202,B_203] : k5_xboole_0(A_202,k5_xboole_0(B_203,k5_xboole_0(A_202,B_203))) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_666,c_38])).

tff(c_1094,plain,(
    ! [A_138,C_22] : k5_xboole_0(A_138,k5_xboole_0(A_138,C_22)) = C_22 ),
    inference(demodulation,[status(thm),theory(equality)],[c_1089,c_679])).

tff(c_1535,plain,(
    ! [B_203,A_202] : k5_xboole_0(B_203,k5_xboole_0(A_202,B_203)) = k5_xboole_0(A_202,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1527,c_1094])).

tff(c_1624,plain,(
    ! [B_204,A_205] : k5_xboole_0(B_204,k5_xboole_0(A_205,B_204)) = A_205 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1535])).

tff(c_1606,plain,(
    ! [B_203,A_202] : k5_xboole_0(B_203,k5_xboole_0(A_202,B_203)) = A_202 ),
    inference(demodulation,[status(thm),theory(equality)],[c_34,c_1535])).

tff(c_1627,plain,(
    ! [A_205,B_204] : k5_xboole_0(k5_xboole_0(A_205,B_204),A_205) = B_204 ),
    inference(superposition,[status(thm),theory(equality)],[c_1624,c_1606])).

tff(c_2110,plain,(
    ! [B_218,A_217] : k5_xboole_0(k4_xboole_0(B_218,A_217),A_217) = k2_xboole_0(A_217,B_218) ),
    inference(superposition,[status(thm),theory(equality)],[c_2101,c_1627])).

tff(c_2,plain,(
    ! [B_2,A_1] : k3_xboole_0(B_2,A_1) = k3_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_214,plain,(
    ! [B_2,A_1] : k5_xboole_0(B_2,k3_xboole_0(A_1,B_2)) = k4_xboole_0(B_2,A_1) ),
    inference(superposition,[status(thm),theory(equality)],[c_2,c_202])).

tff(c_2300,plain,(
    ! [B_225,A_226] : k5_xboole_0(B_225,k4_xboole_0(B_225,A_226)) = k3_xboole_0(A_226,B_225) ),
    inference(superposition,[status(thm),theory(equality)],[c_214,c_1433])).

tff(c_2814,plain,(
    ! [B_240,A_241] : k5_xboole_0(k4_xboole_0(B_240,A_241),k3_xboole_0(A_241,B_240)) = B_240 ),
    inference(superposition,[status(thm),theory(equality)],[c_2300,c_1606])).

tff(c_3199,plain,(
    ! [A_249,B_250] : k5_xboole_0(k3_xboole_0(A_249,B_250),B_250) = k4_xboole_0(B_250,A_249) ),
    inference(superposition,[status(thm),theory(equality)],[c_2814,c_1606])).

tff(c_32,plain,(
    ! [A_15,B_16] : k5_xboole_0(A_15,k3_xboole_0(A_15,B_16)) = k4_xboole_0(A_15,B_16) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_435,plain,(
    ! [A_121,B_122,C_123] : k5_xboole_0(k5_xboole_0(A_121,B_122),C_123) = k5_xboole_0(A_121,k5_xboole_0(B_122,C_123)) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_491,plain,(
    ! [A_15,B_16,C_123] : k5_xboole_0(A_15,k5_xboole_0(k3_xboole_0(A_15,B_16),C_123)) = k5_xboole_0(k4_xboole_0(A_15,B_16),C_123) ),
    inference(superposition,[status(thm),theory(equality)],[c_32,c_435])).

tff(c_3205,plain,(
    ! [A_249,B_250] : k5_xboole_0(k4_xboole_0(A_249,B_250),B_250) = k5_xboole_0(A_249,k4_xboole_0(B_250,A_249)) ),
    inference(superposition,[status(thm),theory(equality)],[c_3199,c_491])).

tff(c_3262,plain,(
    ! [B_250,A_249] : k2_xboole_0(B_250,A_249) = k2_xboole_0(A_249,B_250) ),
    inference(demodulation,[status(thm),theory(equality)],[c_2110,c_40,c_3205])).

tff(c_66,plain,(
    r1_tarski(k2_xboole_0(k1_tarski('#skF_4'),'#skF_5'),'#skF_5') ),
    inference(cnfTransformation,[status(thm)],[f_90])).

tff(c_293,plain,(
    ! [B_91,A_92] :
      ( B_91 = A_92
      | ~ r1_tarski(B_91,A_92)
      | ~ r1_tarski(A_92,B_91) ) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_303,plain,
    ( k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5'
    | ~ r1_tarski('#skF_5',k2_xboole_0(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(resolution,[status(thm)],[c_66,c_293])).

tff(c_320,plain,(
    ~ r1_tarski('#skF_5',k2_xboole_0(k1_tarski('#skF_4'),'#skF_5')) ),
    inference(splitLeft,[status(thm)],[c_303])).

tff(c_3276,plain,(
    ~ r1_tarski('#skF_5',k2_xboole_0('#skF_5',k1_tarski('#skF_4'))) ),
    inference(demodulation,[status(thm),theory(equality)],[c_3262,c_320])).

tff(c_3280,plain,(
    $false ),
    inference(demodulation,[status(thm),theory(equality)],[c_36,c_3276])).

tff(c_3281,plain,(
    k2_xboole_0(k1_tarski('#skF_4'),'#skF_5') = '#skF_5' ),
    inference(splitRight,[status(thm)],[c_303])).

tff(c_42,plain,(
    ! [A_25] : k2_tarski(A_25,A_25) = k1_tarski(A_25) ),
    inference(cnfTransformation,[status(thm)],[f_65])).

tff(c_183,plain,(
    ! [B_76,C_77,A_78] :
      ( r2_hidden(B_76,C_77)
      | ~ r1_tarski(k2_tarski(A_78,B_76),C_77) ) ),
    inference(cnfTransformation,[status(thm)],[f_85])).

tff(c_271,plain,(
    ! [A_87,C_88] :
      ( r2_hidden(A_87,C_88)
      | ~ r1_tarski(k1_tarski(A_87),C_88) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_42,c_183])).

tff(c_285,plain,(
    ! [A_87,B_19] : r2_hidden(A_87,k2_xboole_0(k1_tarski(A_87),B_19)) ),
    inference(resolution,[status(thm)],[c_36,c_271])).

tff(c_3288,plain,(
    r2_hidden('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_3281,c_285])).

tff(c_3295,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_3288])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.00/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.12/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox2/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox2/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n025.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:23:35 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.36  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.16/1.75  % SZS status Theorem for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.76  
% 4.16/1.76  % SZS output start CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.76  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k3_tarski > k1_tarski > k1_xboole_0 > #skF_1 > #skF_5 > #skF_2 > #skF_4 > #skF_3
% 4.16/1.76  
% 4.16/1.76  %Foreground sorts:
% 4.16/1.76  
% 4.16/1.76  
% 4.16/1.76  %Background operators:
% 4.16/1.76  
% 4.16/1.76  
% 4.16/1.76  %Foreground operators:
% 4.16/1.76  tff('#skF_1', type, '#skF_1': ($i * $i * $i) > $i).
% 4.16/1.76  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.16/1.76  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.16/1.76  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.16/1.76  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.16/1.76  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.16/1.76  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.16/1.76  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.16/1.76  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 4.16/1.76  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.16/1.76  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.16/1.76  tff('#skF_5', type, '#skF_5': $i).
% 4.16/1.76  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.16/1.76  tff('#skF_2', type, '#skF_2': ($i * $i * $i) > $i).
% 4.16/1.76  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.16/1.76  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.16/1.76  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.16/1.76  tff(k3_tarski, type, k3_tarski: $i > $i).
% 4.16/1.76  tff('#skF_4', type, '#skF_4': $i).
% 4.16/1.76  tff('#skF_3', type, '#skF_3': $i > $i).
% 4.16/1.76  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.16/1.76  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.16/1.76  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.16/1.76  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.16/1.76  
% 4.16/1.78  tff(f_90, negated_conjecture, ~(![A, B]: (r1_tarski(k2_xboole_0(k1_tarski(A), B), B) => r2_hidden(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t45_zfmisc_1)).
% 4.16/1.78  tff(f_59, axiom, (![A, B]: r1_tarski(A, k2_xboole_0(A, B))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_1)).
% 4.16/1.78  tff(f_63, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.16/1.78  tff(f_57, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t5_boole)).
% 4.16/1.78  tff(f_47, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.16/1.78  tff(f_37, axiom, (![A, B, C]: ((C = k4_xboole_0(A, B)) <=> (![D]: (r2_hidden(D, C) <=> (r2_hidden(D, A) & ~r2_hidden(D, B)))))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d5_xboole_0)).
% 4.16/1.78  tff(f_39, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.16/1.78  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.16/1.78  tff(f_61, axiom, (![A, B, C]: (k5_xboole_0(k5_xboole_0(A, B), C) = k5_xboole_0(A, k5_xboole_0(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t91_xboole_1)).
% 4.16/1.78  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 4.16/1.78  tff(f_53, axiom, (![A, B]: ((A = B) <=> (r1_tarski(A, B) & r1_tarski(B, A)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', d10_xboole_0)).
% 4.16/1.78  tff(f_65, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t69_enumset1)).
% 4.16/1.78  tff(f_85, axiom, (![A, B, C]: (r1_tarski(k2_tarski(A, B), C) <=> (r2_hidden(A, C) & r2_hidden(B, C)))), file('/export/starexec/sandbox2/benchmark/theBenchmark.p', t38_zfmisc_1)).
% 4.16/1.78  tff(c_64, plain, (~r2_hidden('#skF_4', '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.16/1.78  tff(c_36, plain, (![A_18, B_19]: (r1_tarski(A_18, k2_xboole_0(A_18, B_19)))), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.16/1.78  tff(c_40, plain, (![A_23, B_24]: (k5_xboole_0(A_23, k4_xboole_0(B_24, A_23))=k2_xboole_0(A_23, B_24))), inference(cnfTransformation, [status(thm)], [f_63])).
% 4.16/1.78  tff(c_34, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.16/1.78  tff(c_24, plain, (![A_11]: (r2_hidden('#skF_3'(A_11), A_11) | k1_xboole_0=A_11)), inference(cnfTransformation, [status(thm)], [f_47])).
% 4.16/1.78  tff(c_177, plain, (![D_73, A_74, B_75]: (r2_hidden(D_73, A_74) | ~r2_hidden(D_73, k4_xboole_0(A_74, B_75)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.16/1.78  tff(c_615, plain, (![A_135, B_136]: (r2_hidden('#skF_3'(k4_xboole_0(A_135, B_136)), A_135) | k4_xboole_0(A_135, B_136)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_177])).
% 4.16/1.78  tff(c_351, plain, (![D_104, B_105, A_106]: (~r2_hidden(D_104, B_105) | ~r2_hidden(D_104, k4_xboole_0(A_106, B_105)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 4.16/1.78  tff(c_359, plain, (![A_106, B_105]: (~r2_hidden('#skF_3'(k4_xboole_0(A_106, B_105)), B_105) | k4_xboole_0(A_106, B_105)=k1_xboole_0)), inference(resolution, [status(thm)], [c_24, c_351])).
% 4.16/1.78  tff(c_634, plain, (![A_135]: (k4_xboole_0(A_135, A_135)=k1_xboole_0)), inference(resolution, [status(thm)], [c_615, c_359])).
% 4.16/1.78  tff(c_22, plain, (![A_9]: (k3_xboole_0(A_9, A_9)=A_9)), inference(cnfTransformation, [status(thm)], [f_39])).
% 4.16/1.78  tff(c_202, plain, (![A_79, B_80]: (k5_xboole_0(A_79, k3_xboole_0(A_79, B_80))=k4_xboole_0(A_79, B_80))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.16/1.78  tff(c_217, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k4_xboole_0(A_9, A_9))), inference(superposition, [status(thm), theory('equality')], [c_22, c_202])).
% 4.16/1.78  tff(c_640, plain, (![A_9]: (k5_xboole_0(A_9, A_9)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_634, c_217])).
% 4.16/1.78  tff(c_666, plain, (![A_138]: (k5_xboole_0(A_138, A_138)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_634, c_217])).
% 4.16/1.78  tff(c_38, plain, (![A_20, B_21, C_22]: (k5_xboole_0(k5_xboole_0(A_20, B_21), C_22)=k5_xboole_0(A_20, k5_xboole_0(B_21, C_22)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.16/1.78  tff(c_1015, plain, (![A_170, C_171]: (k5_xboole_0(A_170, k5_xboole_0(A_170, C_171))=k5_xboole_0(k1_xboole_0, C_171))), inference(superposition, [status(thm), theory('equality')], [c_666, c_38])).
% 4.16/1.78  tff(c_1052, plain, (![A_9]: (k5_xboole_0(k1_xboole_0, A_9)=k5_xboole_0(A_9, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_640, c_1015])).
% 4.16/1.78  tff(c_1089, plain, (![A_9]: (k5_xboole_0(k1_xboole_0, A_9)=A_9)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1052])).
% 4.16/1.78  tff(c_679, plain, (![A_138, C_22]: (k5_xboole_0(A_138, k5_xboole_0(A_138, C_22))=k5_xboole_0(k1_xboole_0, C_22))), inference(superposition, [status(thm), theory('equality')], [c_666, c_38])).
% 4.16/1.78  tff(c_1433, plain, (![A_195, C_196]: (k5_xboole_0(A_195, k5_xboole_0(A_195, C_196))=C_196)), inference(demodulation, [status(thm), theory('equality')], [c_1089, c_679])).
% 4.16/1.78  tff(c_2101, plain, (![A_217, B_218]: (k5_xboole_0(A_217, k2_xboole_0(A_217, B_218))=k4_xboole_0(B_218, A_217))), inference(superposition, [status(thm), theory('equality')], [c_40, c_1433])).
% 4.16/1.78  tff(c_1527, plain, (![A_202, B_203]: (k5_xboole_0(A_202, k5_xboole_0(B_203, k5_xboole_0(A_202, B_203)))=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_666, c_38])).
% 4.16/1.78  tff(c_1094, plain, (![A_138, C_22]: (k5_xboole_0(A_138, k5_xboole_0(A_138, C_22))=C_22)), inference(demodulation, [status(thm), theory('equality')], [c_1089, c_679])).
% 4.16/1.78  tff(c_1535, plain, (![B_203, A_202]: (k5_xboole_0(B_203, k5_xboole_0(A_202, B_203))=k5_xboole_0(A_202, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_1527, c_1094])).
% 4.16/1.78  tff(c_1624, plain, (![B_204, A_205]: (k5_xboole_0(B_204, k5_xboole_0(A_205, B_204))=A_205)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1535])).
% 4.16/1.78  tff(c_1606, plain, (![B_203, A_202]: (k5_xboole_0(B_203, k5_xboole_0(A_202, B_203))=A_202)), inference(demodulation, [status(thm), theory('equality')], [c_34, c_1535])).
% 4.16/1.78  tff(c_1627, plain, (![A_205, B_204]: (k5_xboole_0(k5_xboole_0(A_205, B_204), A_205)=B_204)), inference(superposition, [status(thm), theory('equality')], [c_1624, c_1606])).
% 4.16/1.78  tff(c_2110, plain, (![B_218, A_217]: (k5_xboole_0(k4_xboole_0(B_218, A_217), A_217)=k2_xboole_0(A_217, B_218))), inference(superposition, [status(thm), theory('equality')], [c_2101, c_1627])).
% 4.16/1.78  tff(c_2, plain, (![B_2, A_1]: (k3_xboole_0(B_2, A_1)=k3_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 4.16/1.78  tff(c_214, plain, (![B_2, A_1]: (k5_xboole_0(B_2, k3_xboole_0(A_1, B_2))=k4_xboole_0(B_2, A_1))), inference(superposition, [status(thm), theory('equality')], [c_2, c_202])).
% 4.16/1.78  tff(c_2300, plain, (![B_225, A_226]: (k5_xboole_0(B_225, k4_xboole_0(B_225, A_226))=k3_xboole_0(A_226, B_225))), inference(superposition, [status(thm), theory('equality')], [c_214, c_1433])).
% 4.16/1.78  tff(c_2814, plain, (![B_240, A_241]: (k5_xboole_0(k4_xboole_0(B_240, A_241), k3_xboole_0(A_241, B_240))=B_240)), inference(superposition, [status(thm), theory('equality')], [c_2300, c_1606])).
% 4.16/1.78  tff(c_3199, plain, (![A_249, B_250]: (k5_xboole_0(k3_xboole_0(A_249, B_250), B_250)=k4_xboole_0(B_250, A_249))), inference(superposition, [status(thm), theory('equality')], [c_2814, c_1606])).
% 4.16/1.78  tff(c_32, plain, (![A_15, B_16]: (k5_xboole_0(A_15, k3_xboole_0(A_15, B_16))=k4_xboole_0(A_15, B_16))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.16/1.78  tff(c_435, plain, (![A_121, B_122, C_123]: (k5_xboole_0(k5_xboole_0(A_121, B_122), C_123)=k5_xboole_0(A_121, k5_xboole_0(B_122, C_123)))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.16/1.78  tff(c_491, plain, (![A_15, B_16, C_123]: (k5_xboole_0(A_15, k5_xboole_0(k3_xboole_0(A_15, B_16), C_123))=k5_xboole_0(k4_xboole_0(A_15, B_16), C_123))), inference(superposition, [status(thm), theory('equality')], [c_32, c_435])).
% 4.16/1.78  tff(c_3205, plain, (![A_249, B_250]: (k5_xboole_0(k4_xboole_0(A_249, B_250), B_250)=k5_xboole_0(A_249, k4_xboole_0(B_250, A_249)))), inference(superposition, [status(thm), theory('equality')], [c_3199, c_491])).
% 4.16/1.78  tff(c_3262, plain, (![B_250, A_249]: (k2_xboole_0(B_250, A_249)=k2_xboole_0(A_249, B_250))), inference(demodulation, [status(thm), theory('equality')], [c_2110, c_40, c_3205])).
% 4.16/1.78  tff(c_66, plain, (r1_tarski(k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'), '#skF_5')), inference(cnfTransformation, [status(thm)], [f_90])).
% 4.16/1.78  tff(c_293, plain, (![B_91, A_92]: (B_91=A_92 | ~r1_tarski(B_91, A_92) | ~r1_tarski(A_92, B_91))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.16/1.78  tff(c_303, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5' | ~r1_tarski('#skF_5', k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'))), inference(resolution, [status(thm)], [c_66, c_293])).
% 4.16/1.78  tff(c_320, plain, (~r1_tarski('#skF_5', k2_xboole_0(k1_tarski('#skF_4'), '#skF_5'))), inference(splitLeft, [status(thm)], [c_303])).
% 4.16/1.78  tff(c_3276, plain, (~r1_tarski('#skF_5', k2_xboole_0('#skF_5', k1_tarski('#skF_4')))), inference(demodulation, [status(thm), theory('equality')], [c_3262, c_320])).
% 4.16/1.78  tff(c_3280, plain, $false, inference(demodulation, [status(thm), theory('equality')], [c_36, c_3276])).
% 4.16/1.78  tff(c_3281, plain, (k2_xboole_0(k1_tarski('#skF_4'), '#skF_5')='#skF_5'), inference(splitRight, [status(thm)], [c_303])).
% 4.16/1.78  tff(c_42, plain, (![A_25]: (k2_tarski(A_25, A_25)=k1_tarski(A_25))), inference(cnfTransformation, [status(thm)], [f_65])).
% 4.16/1.78  tff(c_183, plain, (![B_76, C_77, A_78]: (r2_hidden(B_76, C_77) | ~r1_tarski(k2_tarski(A_78, B_76), C_77))), inference(cnfTransformation, [status(thm)], [f_85])).
% 4.16/1.78  tff(c_271, plain, (![A_87, C_88]: (r2_hidden(A_87, C_88) | ~r1_tarski(k1_tarski(A_87), C_88))), inference(superposition, [status(thm), theory('equality')], [c_42, c_183])).
% 4.16/1.78  tff(c_285, plain, (![A_87, B_19]: (r2_hidden(A_87, k2_xboole_0(k1_tarski(A_87), B_19)))), inference(resolution, [status(thm)], [c_36, c_271])).
% 4.16/1.78  tff(c_3288, plain, (r2_hidden('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_3281, c_285])).
% 4.16/1.78  tff(c_3295, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_3288])).
% 4.16/1.78  % SZS output end CNFRefutation for /export/starexec/sandbox2/benchmark/theBenchmark.p
% 4.16/1.78  
% 4.16/1.78  Inference rules
% 4.16/1.78  ----------------------
% 4.16/1.78  #Ref     : 0
% 4.16/1.78  #Sup     : 761
% 4.16/1.78  #Fact    : 0
% 4.16/1.78  #Define  : 0
% 4.16/1.78  #Split   : 1
% 4.16/1.78  #Chain   : 0
% 4.16/1.78  #Close   : 0
% 4.16/1.78  
% 4.16/1.78  Ordering : KBO
% 4.16/1.78  
% 4.16/1.78  Simplification rules
% 4.16/1.78  ----------------------
% 4.16/1.78  #Subsume      : 29
% 4.16/1.78  #Demod        : 541
% 4.16/1.78  #Tautology    : 511
% 4.16/1.78  #SimpNegUnit  : 5
% 4.16/1.78  #BackRed      : 13
% 4.16/1.78  
% 4.16/1.78  #Partial instantiations: 0
% 4.16/1.78  #Strategies tried      : 1
% 4.16/1.78  
% 4.16/1.78  Timing (in seconds)
% 4.16/1.78  ----------------------
% 4.16/1.78  Preprocessing        : 0.33
% 4.16/1.78  Parsing              : 0.17
% 4.16/1.78  CNF conversion       : 0.02
% 4.16/1.78  Main loop            : 0.64
% 4.16/1.78  Inferencing          : 0.22
% 4.16/1.78  Reduction            : 0.25
% 4.16/1.78  Demodulation         : 0.20
% 4.16/1.78  BG Simplification    : 0.03
% 4.16/1.78  Subsumption          : 0.10
% 4.16/1.78  Abstraction          : 0.03
% 4.16/1.78  MUC search           : 0.00
% 4.16/1.78  Cooper               : 0.00
% 4.16/1.78  Total                : 1.00
% 4.16/1.78  Index Insertion      : 0.00
% 4.16/1.78  Index Deletion       : 0.00
% 4.16/1.78  Index Matching       : 0.00
% 4.16/1.78  BG Taut test         : 0.00
%------------------------------------------------------------------------------

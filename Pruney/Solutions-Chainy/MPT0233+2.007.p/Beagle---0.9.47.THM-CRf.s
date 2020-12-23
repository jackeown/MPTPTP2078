%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n017.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:24 EST 2020

% Result     : Theorem 3.72s
% Output     : CNFRefutation 3.72s
% Verified   : 
% Statistics : Number of formulae       :   83 (  93 expanded)
%              Number of leaves         :   42 (  49 expanded)
%              Depth                    :   13
%              Number of atoms          :   81 (  96 expanded)
%              Number of equality atoms :   59 (  71 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1

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

tff('#skF_4',type,(
    '#skF_4': ( $i * $i * $i ) > $i )).

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

tff('#skF_2',type,(
    '#skF_2': ( $i * $i * $i * $i ) > $i )).

tff('#skF_6',type,(
    '#skF_6': $i )).

tff(k1_enumset1,type,(
    k1_enumset1: ( $i * $i * $i ) > $i )).

tff(k4_enumset1,type,(
    k4_enumset1: ( $i * $i * $i * $i * $i * $i ) > $i )).

tff(k6_enumset1,type,(
    k6_enumset1: ( $i * $i * $i * $i * $i * $i * $i * $i ) > $i )).

tff('#skF_8',type,(
    '#skF_8': $i )).

tff('#nlpp_001',type,(
    '#nlpp': ( $rat * $rat ) > $rat )).

tff('#skF_3',type,(
    '#skF_3': ( $i * $i * $i ) > $i )).

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

tff(f_116,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_83,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_81,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_75,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_47,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_43,axiom,(
    ! [A] : k3_xboole_0(A,k1_xboole_0) = k1_xboole_0 ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t2_boole)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_45,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_106,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_41,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k3_xboole_0(B,C))
     => r1_tarski(A,B) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_xboole_1)).

tff(f_49,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_64,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_73,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(c_94,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_92,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_72,plain,(
    ! [A_45,B_46,C_47] : k2_enumset1(A_45,A_45,B_46,C_47) = k1_enumset1(A_45,B_46,C_47) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_70,plain,(
    ! [A_43,B_44] : k1_enumset1(A_43,A_43,B_44) = k2_tarski(A_43,B_44) ),
    inference(cnfTransformation,[status(thm)],[f_81])).

tff(c_1148,plain,(
    ! [A_171,B_172,C_173,D_174] : k2_xboole_0(k1_enumset1(A_171,B_172,C_173),k1_tarski(D_174)) = k2_enumset1(A_171,B_172,C_173,D_174) ),
    inference(cnfTransformation,[status(thm)],[f_75])).

tff(c_1163,plain,(
    ! [A_43,B_44,D_174] : k2_xboole_0(k2_tarski(A_43,B_44),k1_tarski(D_174)) = k2_enumset1(A_43,A_43,B_44,D_174) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1148])).

tff(c_1340,plain,(
    ! [A_185,B_186,D_187] : k2_xboole_0(k2_tarski(A_185,B_186),k1_tarski(D_187)) = k1_enumset1(A_185,B_186,D_187) ),
    inference(demodulation,[status(thm),theory(equality)],[c_72,c_1163])).

tff(c_18,plain,(
    ! [A_17] : k5_xboole_0(A_17,k1_xboole_0) = A_17 ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_14,plain,(
    ! [A_14] : k3_xboole_0(A_14,k1_xboole_0) = k1_xboole_0 ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_381,plain,(
    ! [A_115,B_116] : k5_xboole_0(A_115,k3_xboole_0(A_115,B_116)) = k4_xboole_0(A_115,B_116) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_405,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = k4_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_14,c_381])).

tff(c_409,plain,(
    ! [A_14] : k4_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_405])).

tff(c_455,plain,(
    ! [A_120,B_121] : k4_xboole_0(A_120,k4_xboole_0(A_120,B_121)) = k3_xboole_0(A_120,B_121) ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_481,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k3_xboole_0(A_14,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_409,c_455])).

tff(c_487,plain,(
    ! [A_14] : k4_xboole_0(A_14,A_14) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_14,c_481])).

tff(c_6,plain,(
    ! [A_5] : k3_xboole_0(A_5,A_5) = A_5 ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_402,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k4_xboole_0(A_5,A_5) ),
    inference(superposition,[status(thm),theory(equality)],[c_6,c_381])).

tff(c_508,plain,(
    ! [A_5] : k5_xboole_0(A_5,A_5) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_487,c_402])).

tff(c_88,plain,(
    ! [B_71,C_72] : r1_tarski(k1_tarski(B_71),k2_tarski(B_71,C_72)) ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_96,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_116])).

tff(c_303,plain,(
    ! [A_106,B_107] :
      ( k3_xboole_0(A_106,B_107) = A_106
      | ~ r1_tarski(A_106,B_107) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_331,plain,(
    k3_xboole_0(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) = k2_tarski('#skF_5','#skF_6') ),
    inference(resolution,[status(thm)],[c_96,c_303])).

tff(c_4,plain,(
    ! [B_4,A_3] : k3_xboole_0(B_4,A_3) = k3_xboole_0(A_3,B_4) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_357,plain,(
    ! [A_110,B_111,C_112] :
      ( r1_tarski(A_110,B_111)
      | ~ r1_tarski(A_110,k3_xboole_0(B_111,C_112)) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_902,plain,(
    ! [A_148,A_149,B_150] :
      ( r1_tarski(A_148,A_149)
      | ~ r1_tarski(A_148,k3_xboole_0(B_150,A_149)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_357])).

tff(c_935,plain,(
    ! [A_154] :
      ( r1_tarski(A_154,k2_tarski('#skF_7','#skF_8'))
      | ~ r1_tarski(A_154,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_331,c_902])).

tff(c_12,plain,(
    ! [A_12,B_13] :
      ( k3_xboole_0(A_12,B_13) = A_12
      | ~ r1_tarski(A_12,B_13) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_1056,plain,(
    ! [A_170] :
      ( k3_xboole_0(A_170,k2_tarski('#skF_7','#skF_8')) = A_170
      | ~ r1_tarski(A_170,k2_tarski('#skF_5','#skF_6')) ) ),
    inference(resolution,[status(thm)],[c_935,c_12])).

tff(c_1086,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_tarski('#skF_5') ),
    inference(resolution,[status(thm)],[c_88,c_1056])).

tff(c_8,plain,(
    ! [A_7,B_8] : k5_xboole_0(A_7,k3_xboole_0(A_7,B_8)) = k4_xboole_0(A_7,B_8) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_1127,plain,(
    k5_xboole_0(k1_tarski('#skF_5'),k1_tarski('#skF_5')) = k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1086,c_8])).

tff(c_1133,plain,(
    k4_xboole_0(k1_tarski('#skF_5'),k2_tarski('#skF_7','#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_508,c_1127])).

tff(c_20,plain,(
    ! [A_18,B_19] : k5_xboole_0(A_18,k4_xboole_0(B_19,A_18)) = k2_xboole_0(A_18,B_19) ),
    inference(cnfTransformation,[status(thm)],[f_49])).

tff(c_1138,plain,(
    k2_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_5')) = k5_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1133,c_20])).

tff(c_1144,plain,(
    k2_xboole_0(k2_tarski('#skF_7','#skF_8'),k1_tarski('#skF_5')) = k2_tarski('#skF_7','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1138])).

tff(c_1349,plain,(
    k1_enumset1('#skF_7','#skF_8','#skF_5') = k2_tarski('#skF_7','#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_1340,c_1144])).

tff(c_24,plain,(
    ! [E_26,A_20,B_21] : r2_hidden(E_26,k1_enumset1(A_20,B_21,E_26)) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1666,plain,(
    r2_hidden('#skF_5',k2_tarski('#skF_7','#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_1349,c_24])).

tff(c_46,plain,(
    ! [D_32,B_28,A_27] :
      ( D_32 = B_28
      | D_32 = A_27
      | ~ r2_hidden(D_32,k2_tarski(A_27,B_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_73])).

tff(c_1699,plain,
    ( '#skF_5' = '#skF_8'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_1666,c_46])).

tff(c_1703,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_94,c_92,c_1699])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.14/0.34  % Computer   : n017.cluster.edu
% 0.14/0.34  % Model      : x86_64 x86_64
% 0.14/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.14/0.34  % Memory     : 8042.1875MB
% 0.14/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.14/0.34  % CPULimit   : 60
% 0.14/0.34  % DateTime   : Tue Dec  1 20:44:46 EST 2020
% 0.14/0.34  % CPUTime    : 
% 0.14/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 3.72/1.70  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.70  
% 3.72/1.70  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.71  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 3.72/1.71  
% 3.72/1.71  %Foreground sorts:
% 3.72/1.71  
% 3.72/1.71  
% 3.72/1.71  %Background operators:
% 3.72/1.71  
% 3.72/1.71  
% 3.72/1.71  %Foreground operators:
% 3.72/1.71  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 3.72/1.71  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 3.72/1.71  tff(k1_tarski, type, k1_tarski: $i > $i).
% 3.72/1.71  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 3.72/1.71  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 3.72/1.71  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 3.72/1.71  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 3.72/1.71  tff('#skF_7', type, '#skF_7': $i).
% 3.72/1.71  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 3.72/1.71  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 3.72/1.71  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 3.72/1.71  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 3.72/1.71  tff('#skF_5', type, '#skF_5': $i).
% 3.72/1.71  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 3.72/1.71  tff('#skF_6', type, '#skF_6': $i).
% 3.72/1.71  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 3.72/1.71  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 3.72/1.71  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 3.72/1.71  tff('#skF_8', type, '#skF_8': $i).
% 3.72/1.71  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 3.72/1.71  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 3.72/1.71  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 3.72/1.71  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 3.72/1.71  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 3.72/1.71  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 3.72/1.71  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 3.72/1.71  
% 3.72/1.72  tff(f_116, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 3.72/1.72  tff(f_83, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 3.72/1.72  tff(f_81, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 3.72/1.72  tff(f_75, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 3.72/1.72  tff(f_47, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 3.72/1.72  tff(f_43, axiom, (![A]: (k3_xboole_0(A, k1_xboole_0) = k1_xboole_0)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t2_boole)).
% 3.72/1.72  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 3.72/1.72  tff(f_45, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 3.72/1.72  tff(f_31, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 3.72/1.72  tff(f_106, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 3.72/1.72  tff(f_41, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 3.72/1.72  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 3.72/1.72  tff(f_37, axiom, (![A, B, C]: (r1_tarski(A, k3_xboole_0(B, C)) => r1_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_xboole_1)).
% 3.72/1.72  tff(f_49, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 3.72/1.72  tff(f_64, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 3.72/1.72  tff(f_73, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 3.72/1.72  tff(c_94, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.72/1.72  tff(c_92, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.72/1.72  tff(c_72, plain, (![A_45, B_46, C_47]: (k2_enumset1(A_45, A_45, B_46, C_47)=k1_enumset1(A_45, B_46, C_47))), inference(cnfTransformation, [status(thm)], [f_83])).
% 3.72/1.72  tff(c_70, plain, (![A_43, B_44]: (k1_enumset1(A_43, A_43, B_44)=k2_tarski(A_43, B_44))), inference(cnfTransformation, [status(thm)], [f_81])).
% 3.72/1.72  tff(c_1148, plain, (![A_171, B_172, C_173, D_174]: (k2_xboole_0(k1_enumset1(A_171, B_172, C_173), k1_tarski(D_174))=k2_enumset1(A_171, B_172, C_173, D_174))), inference(cnfTransformation, [status(thm)], [f_75])).
% 3.72/1.72  tff(c_1163, plain, (![A_43, B_44, D_174]: (k2_xboole_0(k2_tarski(A_43, B_44), k1_tarski(D_174))=k2_enumset1(A_43, A_43, B_44, D_174))), inference(superposition, [status(thm), theory('equality')], [c_70, c_1148])).
% 3.72/1.72  tff(c_1340, plain, (![A_185, B_186, D_187]: (k2_xboole_0(k2_tarski(A_185, B_186), k1_tarski(D_187))=k1_enumset1(A_185, B_186, D_187))), inference(demodulation, [status(thm), theory('equality')], [c_72, c_1163])).
% 3.72/1.72  tff(c_18, plain, (![A_17]: (k5_xboole_0(A_17, k1_xboole_0)=A_17)), inference(cnfTransformation, [status(thm)], [f_47])).
% 3.72/1.72  tff(c_14, plain, (![A_14]: (k3_xboole_0(A_14, k1_xboole_0)=k1_xboole_0)), inference(cnfTransformation, [status(thm)], [f_43])).
% 3.72/1.72  tff(c_381, plain, (![A_115, B_116]: (k5_xboole_0(A_115, k3_xboole_0(A_115, B_116))=k4_xboole_0(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.72/1.72  tff(c_405, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=k4_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_14, c_381])).
% 3.72/1.72  tff(c_409, plain, (![A_14]: (k4_xboole_0(A_14, k1_xboole_0)=A_14)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_405])).
% 3.72/1.72  tff(c_455, plain, (![A_120, B_121]: (k4_xboole_0(A_120, k4_xboole_0(A_120, B_121))=k3_xboole_0(A_120, B_121))), inference(cnfTransformation, [status(thm)], [f_45])).
% 3.72/1.72  tff(c_481, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k3_xboole_0(A_14, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_409, c_455])).
% 3.72/1.72  tff(c_487, plain, (![A_14]: (k4_xboole_0(A_14, A_14)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_14, c_481])).
% 3.72/1.72  tff(c_6, plain, (![A_5]: (k3_xboole_0(A_5, A_5)=A_5)), inference(cnfTransformation, [status(thm)], [f_31])).
% 3.72/1.72  tff(c_402, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k4_xboole_0(A_5, A_5))), inference(superposition, [status(thm), theory('equality')], [c_6, c_381])).
% 3.72/1.72  tff(c_508, plain, (![A_5]: (k5_xboole_0(A_5, A_5)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_487, c_402])).
% 3.72/1.72  tff(c_88, plain, (![B_71, C_72]: (r1_tarski(k1_tarski(B_71), k2_tarski(B_71, C_72)))), inference(cnfTransformation, [status(thm)], [f_106])).
% 3.72/1.72  tff(c_96, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_116])).
% 3.72/1.72  tff(c_303, plain, (![A_106, B_107]: (k3_xboole_0(A_106, B_107)=A_106 | ~r1_tarski(A_106, B_107))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.72/1.72  tff(c_331, plain, (k3_xboole_0(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))=k2_tarski('#skF_5', '#skF_6')), inference(resolution, [status(thm)], [c_96, c_303])).
% 3.72/1.72  tff(c_4, plain, (![B_4, A_3]: (k3_xboole_0(B_4, A_3)=k3_xboole_0(A_3, B_4))), inference(cnfTransformation, [status(thm)], [f_29])).
% 3.72/1.72  tff(c_357, plain, (![A_110, B_111, C_112]: (r1_tarski(A_110, B_111) | ~r1_tarski(A_110, k3_xboole_0(B_111, C_112)))), inference(cnfTransformation, [status(thm)], [f_37])).
% 3.72/1.72  tff(c_902, plain, (![A_148, A_149, B_150]: (r1_tarski(A_148, A_149) | ~r1_tarski(A_148, k3_xboole_0(B_150, A_149)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_357])).
% 3.72/1.72  tff(c_935, plain, (![A_154]: (r1_tarski(A_154, k2_tarski('#skF_7', '#skF_8')) | ~r1_tarski(A_154, k2_tarski('#skF_5', '#skF_6')))), inference(superposition, [status(thm), theory('equality')], [c_331, c_902])).
% 3.72/1.72  tff(c_12, plain, (![A_12, B_13]: (k3_xboole_0(A_12, B_13)=A_12 | ~r1_tarski(A_12, B_13))), inference(cnfTransformation, [status(thm)], [f_41])).
% 3.72/1.72  tff(c_1056, plain, (![A_170]: (k3_xboole_0(A_170, k2_tarski('#skF_7', '#skF_8'))=A_170 | ~r1_tarski(A_170, k2_tarski('#skF_5', '#skF_6')))), inference(resolution, [status(thm)], [c_935, c_12])).
% 3.72/1.72  tff(c_1086, plain, (k3_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_tarski('#skF_5')), inference(resolution, [status(thm)], [c_88, c_1056])).
% 3.72/1.72  tff(c_8, plain, (![A_7, B_8]: (k5_xboole_0(A_7, k3_xboole_0(A_7, B_8))=k4_xboole_0(A_7, B_8))), inference(cnfTransformation, [status(thm)], [f_33])).
% 3.72/1.72  tff(c_1127, plain, (k5_xboole_0(k1_tarski('#skF_5'), k1_tarski('#skF_5'))=k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1086, c_8])).
% 3.72/1.72  tff(c_1133, plain, (k4_xboole_0(k1_tarski('#skF_5'), k2_tarski('#skF_7', '#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_508, c_1127])).
% 3.72/1.72  tff(c_20, plain, (![A_18, B_19]: (k5_xboole_0(A_18, k4_xboole_0(B_19, A_18))=k2_xboole_0(A_18, B_19))), inference(cnfTransformation, [status(thm)], [f_49])).
% 3.72/1.72  tff(c_1138, plain, (k2_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_5'))=k5_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1133, c_20])).
% 3.72/1.72  tff(c_1144, plain, (k2_xboole_0(k2_tarski('#skF_7', '#skF_8'), k1_tarski('#skF_5'))=k2_tarski('#skF_7', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1138])).
% 3.72/1.72  tff(c_1349, plain, (k1_enumset1('#skF_7', '#skF_8', '#skF_5')=k2_tarski('#skF_7', '#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_1340, c_1144])).
% 3.72/1.72  tff(c_24, plain, (![E_26, A_20, B_21]: (r2_hidden(E_26, k1_enumset1(A_20, B_21, E_26)))), inference(cnfTransformation, [status(thm)], [f_64])).
% 3.72/1.72  tff(c_1666, plain, (r2_hidden('#skF_5', k2_tarski('#skF_7', '#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_1349, c_24])).
% 3.72/1.72  tff(c_46, plain, (![D_32, B_28, A_27]: (D_32=B_28 | D_32=A_27 | ~r2_hidden(D_32, k2_tarski(A_27, B_28)))), inference(cnfTransformation, [status(thm)], [f_73])).
% 3.72/1.72  tff(c_1699, plain, ('#skF_5'='#skF_8' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_1666, c_46])).
% 3.72/1.72  tff(c_1703, plain, $false, inference(negUnitSimplification, [status(thm)], [c_94, c_92, c_1699])).
% 3.72/1.72  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 3.72/1.72  
% 3.72/1.72  Inference rules
% 3.72/1.72  ----------------------
% 3.72/1.72  #Ref     : 0
% 3.72/1.72  #Sup     : 390
% 3.72/1.72  #Fact    : 0
% 3.72/1.72  #Define  : 0
% 3.72/1.72  #Split   : 1
% 3.72/1.72  #Chain   : 0
% 3.72/1.72  #Close   : 0
% 3.72/1.72  
% 3.72/1.72  Ordering : KBO
% 3.72/1.72  
% 3.72/1.72  Simplification rules
% 3.72/1.72  ----------------------
% 3.72/1.72  #Subsume      : 14
% 3.72/1.72  #Demod        : 252
% 3.72/1.72  #Tautology    : 292
% 3.72/1.72  #SimpNegUnit  : 2
% 3.72/1.72  #BackRed      : 38
% 3.72/1.72  
% 3.72/1.72  #Partial instantiations: 0
% 3.72/1.72  #Strategies tried      : 1
% 3.72/1.72  
% 3.72/1.72  Timing (in seconds)
% 3.72/1.72  ----------------------
% 3.72/1.72  Preprocessing        : 0.36
% 3.72/1.72  Parsing              : 0.19
% 3.72/1.72  CNF conversion       : 0.03
% 3.72/1.72  Main loop            : 0.49
% 3.72/1.72  Inferencing          : 0.16
% 3.72/1.72  Reduction            : 0.18
% 3.72/1.72  Demodulation         : 0.14
% 3.72/1.72  BG Simplification    : 0.03
% 3.72/1.72  Subsumption          : 0.08
% 3.72/1.72  Abstraction          : 0.02
% 3.72/1.72  MUC search           : 0.00
% 3.72/1.72  Cooper               : 0.00
% 3.72/1.72  Total                : 0.88
% 3.72/1.72  Index Insertion      : 0.00
% 3.72/1.72  Index Deletion       : 0.00
% 3.72/1.72  Index Matching       : 0.00
% 3.72/1.72  BG Taut test         : 0.00
%------------------------------------------------------------------------------

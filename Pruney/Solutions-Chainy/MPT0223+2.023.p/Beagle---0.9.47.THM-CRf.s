%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n001.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:48:19 EST 2020

% Result     : Theorem 4.47s
% Output     : CNFRefutation 4.54s
% Verified   : 
% Statistics : Number of formulae       :   83 ( 115 expanded)
%              Number of leaves         :   41 (  56 expanded)
%              Depth                    :   16
%              Number of atoms          :   72 ( 112 expanded)
%              Number of equality atoms :   52 (  79 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    3 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_5

%Foreground sorts:

%Background operators:

%Foreground operators:
tff('#skF_6',type,(
    '#skF_6': ( $i * $i ) > $i )).

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

tff(k2_enumset1,type,(
    k2_enumset1: ( $i * $i * $i * $i ) > $i )).

tff(k2_tarski,type,(
    k2_tarski: ( $i * $i ) > $i )).

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

tff('#skF_8',type,(
    '#skF_8': $i )).

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

tff('#skF_5',type,(
    '#skF_5': ( $i * $i ) > $i )).

tff(f_106,negated_conjecture,(
    ~ ! [A,B] :
        ( k3_xboole_0(k1_tarski(A),k1_tarski(B)) = k1_tarski(A)
       => A = B ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t18_zfmisc_1)).

tff(f_91,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_89,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_93,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_87,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k1_enumset1(A,B,C),k1_tarski(D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t46_enumset1)).

tff(f_59,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_55,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : r1_xboole_0(k3_xboole_0(A,B),k5_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l97_xboole_1)).

tff(f_51,axiom,(
    ! [A] :
      ~ ( A != k1_xboole_0
        & ! [B] : ~ r2_hidden(B,A) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t7_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( ~ ( ~ r1_xboole_0(A,B)
          & ! [C] : ~ r2_hidden(C,k3_xboole_0(A,B)) )
      & ~ ( ? [C] : r2_hidden(C,k3_xboole_0(A,B))
          & r1_xboole_0(A,B) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t4_xboole_0)).

tff(f_57,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_61,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_76,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_83,axiom,(
    ! [A,B] :
      ( B = k1_tarski(A)
    <=> ! [C] :
          ( r2_hidden(C,B)
        <=> C = A ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_tarski)).

tff(c_76,plain,(
    '#skF_7' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_64,plain,(
    ! [A_41,B_42] : k1_enumset1(A_41,A_41,B_42) = k2_tarski(A_41,B_42) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_62,plain,(
    ! [A_40] : k2_tarski(A_40,A_40) = k1_tarski(A_40) ),
    inference(cnfTransformation,[status(thm)],[f_89])).

tff(c_66,plain,(
    ! [A_43,B_44,C_45] : k2_enumset1(A_43,A_43,B_44,C_45) = k1_enumset1(A_43,B_44,C_45) ),
    inference(cnfTransformation,[status(thm)],[f_93])).

tff(c_1774,plain,(
    ! [A_166,B_167,C_168,D_169] : k2_xboole_0(k1_enumset1(A_166,B_167,C_168),k1_tarski(D_169)) = k2_enumset1(A_166,B_167,C_168,D_169) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_1792,plain,(
    ! [A_41,B_42,D_169] : k2_xboole_0(k2_tarski(A_41,B_42),k1_tarski(D_169)) = k2_enumset1(A_41,A_41,B_42,D_169) ),
    inference(superposition,[status(thm),theory(equality)],[c_64,c_1774])).

tff(c_3922,plain,(
    ! [A_241,B_242,D_243] : k2_xboole_0(k2_tarski(A_241,B_242),k1_tarski(D_243)) = k1_enumset1(A_241,B_242,D_243) ),
    inference(demodulation,[status(thm),theory(equality)],[c_66,c_1792])).

tff(c_3937,plain,(
    ! [A_40,D_243] : k2_xboole_0(k1_tarski(A_40),k1_tarski(D_243)) = k1_enumset1(A_40,A_40,D_243) ),
    inference(superposition,[status(thm),theory(equality)],[c_62,c_3922])).

tff(c_3941,plain,(
    ! [A_244,D_245] : k2_xboole_0(k1_tarski(A_244),k1_tarski(D_245)) = k2_tarski(A_244,D_245) ),
    inference(demodulation,[status(thm),theory(equality)],[c_64,c_3937])).

tff(c_18,plain,(
    ! [A_18] : k5_xboole_0(A_18,k1_xboole_0) = A_18 ),
    inference(cnfTransformation,[status(thm)],[f_59])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_283,plain,(
    ! [A_99,B_100] : k5_xboole_0(A_99,k3_xboole_0(A_99,B_100)) = k4_xboole_0(A_99,B_100) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_310,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_283])).

tff(c_195,plain,(
    ! [A_90,B_91] : r1_xboole_0(k3_xboole_0(A_90,B_91),k5_xboole_0(A_90,B_91)) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_210,plain,(
    ! [A_3] : r1_xboole_0(A_3,k5_xboole_0(A_3,A_3)) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_195])).

tff(c_314,plain,(
    ! [A_3] : r1_xboole_0(A_3,k4_xboole_0(A_3,A_3)) ),
    inference(demodulation,[status(thm),theory(equality)],[c_310,c_210])).

tff(c_10,plain,(
    ! [A_10] :
      ( r2_hidden('#skF_2'(A_10),A_10)
      | k1_xboole_0 = A_10 ) ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_368,plain,(
    ! [A_104,B_105,C_106] :
      ( ~ r1_xboole_0(A_104,B_105)
      | ~ r2_hidden(C_106,k3_xboole_0(A_104,B_105)) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_401,plain,(
    ! [A_110,B_111] :
      ( ~ r1_xboole_0(A_110,B_111)
      | k3_xboole_0(A_110,B_111) = k1_xboole_0 ) ),
    inference(resolution,[status(thm)],[c_10,c_368])).

tff(c_424,plain,(
    ! [A_3] : k3_xboole_0(A_3,k4_xboole_0(A_3,A_3)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_314,c_401])).

tff(c_431,plain,(
    ! [A_112] : k3_xboole_0(A_112,k4_xboole_0(A_112,A_112)) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_314,c_401])).

tff(c_14,plain,(
    ! [A_14,B_15] : k5_xboole_0(A_14,k3_xboole_0(A_14,B_15)) = k4_xboole_0(A_14,B_15) ),
    inference(cnfTransformation,[status(thm)],[f_55])).

tff(c_439,plain,(
    ! [A_112] : k4_xboole_0(A_112,k4_xboole_0(A_112,A_112)) = k5_xboole_0(A_112,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_431,c_14])).

tff(c_458,plain,(
    ! [A_112] : k4_xboole_0(A_112,k4_xboole_0(A_112,A_112)) = A_112 ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_439])).

tff(c_949,plain,(
    ! [A_127,B_128] : k4_xboole_0(A_127,k4_xboole_0(A_127,B_128)) = k3_xboole_0(A_127,B_128) ),
    inference(cnfTransformation,[status(thm)],[f_57])).

tff(c_974,plain,(
    ! [A_112] : k3_xboole_0(A_112,k4_xboole_0(A_112,A_112)) = k4_xboole_0(A_112,A_112) ),
    inference(superposition,[status(thm),theory(equality)],[c_458,c_949])).

tff(c_985,plain,(
    ! [A_112] : k4_xboole_0(A_112,A_112) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_424,c_974])).

tff(c_992,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_985,c_310])).

tff(c_78,plain,(
    k3_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_tarski('#skF_7') ),
    inference(cnfTransformation,[status(thm)],[f_106])).

tff(c_301,plain,(
    k5_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_7')) = k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_78,c_283])).

tff(c_1076,plain,(
    k4_xboole_0(k1_tarski('#skF_7'),k1_tarski('#skF_8')) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_992,c_301])).

tff(c_20,plain,(
    ! [A_19,B_20] : k5_xboole_0(A_19,k4_xboole_0(B_20,A_19)) = k2_xboole_0(A_19,B_20) ),
    inference(cnfTransformation,[status(thm)],[f_61])).

tff(c_1268,plain,(
    k2_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k5_xboole_0(k1_tarski('#skF_8'),k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_1076,c_20])).

tff(c_1272,plain,(
    k2_xboole_0(k1_tarski('#skF_8'),k1_tarski('#skF_7')) = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_18,c_1268])).

tff(c_3953,plain,(
    k2_tarski('#skF_8','#skF_7') = k1_tarski('#skF_8') ),
    inference(superposition,[status(thm),theory(equality)],[c_3941,c_1272])).

tff(c_171,plain,(
    ! [A_86,B_87] : k1_enumset1(A_86,A_86,B_87) = k2_tarski(A_86,B_87) ),
    inference(cnfTransformation,[status(thm)],[f_91])).

tff(c_24,plain,(
    ! [E_27,A_21,B_22] : r2_hidden(E_27,k1_enumset1(A_21,B_22,E_27)) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_183,plain,(
    ! [B_87,A_86] : r2_hidden(B_87,k2_tarski(A_86,B_87)) ),
    inference(superposition,[status(thm),theory(equality)],[c_171,c_24])).

tff(c_3978,plain,(
    r2_hidden('#skF_7',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_3953,c_183])).

tff(c_46,plain,(
    ! [C_32,A_28] :
      ( C_32 = A_28
      | ~ r2_hidden(C_32,k1_tarski(A_28)) ) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_4057,plain,(
    '#skF_7' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_3978,c_46])).

tff(c_4061,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_76,c_4057])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n001.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 11:27:59 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 4.47/1.84  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.84  
% 4.54/1.84  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.85  %$ r2_hidden > r1_xboole_0 > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_6 > #skF_2 > #skF_7 > #skF_4 > #skF_8 > #skF_3 > #skF_1 > #skF_5
% 4.54/1.85  
% 4.54/1.85  %Foreground sorts:
% 4.54/1.85  
% 4.54/1.85  
% 4.54/1.85  %Background operators:
% 4.54/1.85  
% 4.54/1.85  
% 4.54/1.85  %Foreground operators:
% 4.54/1.85  tff('#skF_6', type, '#skF_6': ($i * $i) > $i).
% 4.54/1.85  tff('#skF_2', type, '#skF_2': $i > $i).
% 4.54/1.85  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 4.54/1.85  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 4.54/1.85  tff(k1_tarski, type, k1_tarski: $i > $i).
% 4.54/1.85  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 4.54/1.85  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 4.54/1.85  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 4.54/1.85  tff('#skF_7', type, '#skF_7': $i).
% 4.54/1.85  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 4.54/1.85  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 4.54/1.85  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 4.54/1.85  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 4.54/1.85  tff(r1_xboole_0, type, r1_xboole_0: ($i * $i) > $o).
% 4.54/1.85  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 4.54/1.85  tff('#skF_4', type, '#skF_4': ($i * $i * $i * $i) > $i).
% 4.54/1.85  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 4.54/1.85  tff('#skF_8', type, '#skF_8': $i).
% 4.54/1.85  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 4.54/1.85  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 4.54/1.85  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 4.54/1.85  tff('#skF_3', type, '#skF_3': ($i * $i * $i * $i) > $i).
% 4.54/1.85  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 4.54/1.85  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 4.54/1.85  tff('#skF_1', type, '#skF_1': ($i * $i) > $i).
% 4.54/1.85  tff('#skF_5', type, '#skF_5': ($i * $i) > $i).
% 4.54/1.85  
% 4.54/1.86  tff(f_106, negated_conjecture, ~(![A, B]: ((k3_xboole_0(k1_tarski(A), k1_tarski(B)) = k1_tarski(A)) => (A = B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t18_zfmisc_1)).
% 4.54/1.86  tff(f_91, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 4.54/1.86  tff(f_89, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 4.54/1.86  tff(f_93, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 4.54/1.86  tff(f_87, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k1_enumset1(A, B, C), k1_tarski(D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t46_enumset1)).
% 4.54/1.86  tff(f_59, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 4.54/1.86  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 4.54/1.86  tff(f_55, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 4.54/1.86  tff(f_53, axiom, (![A, B]: r1_xboole_0(k3_xboole_0(A, B), k5_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l97_xboole_1)).
% 4.54/1.86  tff(f_51, axiom, (![A]: ~(~(A = k1_xboole_0) & (![B]: ~r2_hidden(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t7_xboole_0)).
% 4.54/1.86  tff(f_43, axiom, (![A, B]: (~(~r1_xboole_0(A, B) & (![C]: ~r2_hidden(C, k3_xboole_0(A, B)))) & ~((?[C]: r2_hidden(C, k3_xboole_0(A, B))) & r1_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t4_xboole_0)).
% 4.54/1.86  tff(f_57, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 4.54/1.86  tff(f_61, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 4.54/1.86  tff(f_76, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 4.54/1.86  tff(f_83, axiom, (![A, B]: ((B = k1_tarski(A)) <=> (![C]: (r2_hidden(C, B) <=> (C = A))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_tarski)).
% 4.54/1.86  tff(c_76, plain, ('#skF_7'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.54/1.86  tff(c_64, plain, (![A_41, B_42]: (k1_enumset1(A_41, A_41, B_42)=k2_tarski(A_41, B_42))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.54/1.86  tff(c_62, plain, (![A_40]: (k2_tarski(A_40, A_40)=k1_tarski(A_40))), inference(cnfTransformation, [status(thm)], [f_89])).
% 4.54/1.86  tff(c_66, plain, (![A_43, B_44, C_45]: (k2_enumset1(A_43, A_43, B_44, C_45)=k1_enumset1(A_43, B_44, C_45))), inference(cnfTransformation, [status(thm)], [f_93])).
% 4.54/1.86  tff(c_1774, plain, (![A_166, B_167, C_168, D_169]: (k2_xboole_0(k1_enumset1(A_166, B_167, C_168), k1_tarski(D_169))=k2_enumset1(A_166, B_167, C_168, D_169))), inference(cnfTransformation, [status(thm)], [f_87])).
% 4.54/1.86  tff(c_1792, plain, (![A_41, B_42, D_169]: (k2_xboole_0(k2_tarski(A_41, B_42), k1_tarski(D_169))=k2_enumset1(A_41, A_41, B_42, D_169))), inference(superposition, [status(thm), theory('equality')], [c_64, c_1774])).
% 4.54/1.86  tff(c_3922, plain, (![A_241, B_242, D_243]: (k2_xboole_0(k2_tarski(A_241, B_242), k1_tarski(D_243))=k1_enumset1(A_241, B_242, D_243))), inference(demodulation, [status(thm), theory('equality')], [c_66, c_1792])).
% 4.54/1.86  tff(c_3937, plain, (![A_40, D_243]: (k2_xboole_0(k1_tarski(A_40), k1_tarski(D_243))=k1_enumset1(A_40, A_40, D_243))), inference(superposition, [status(thm), theory('equality')], [c_62, c_3922])).
% 4.54/1.86  tff(c_3941, plain, (![A_244, D_245]: (k2_xboole_0(k1_tarski(A_244), k1_tarski(D_245))=k2_tarski(A_244, D_245))), inference(demodulation, [status(thm), theory('equality')], [c_64, c_3937])).
% 4.54/1.86  tff(c_18, plain, (![A_18]: (k5_xboole_0(A_18, k1_xboole_0)=A_18)), inference(cnfTransformation, [status(thm)], [f_59])).
% 4.54/1.86  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 4.54/1.86  tff(c_283, plain, (![A_99, B_100]: (k5_xboole_0(A_99, k3_xboole_0(A_99, B_100))=k4_xboole_0(A_99, B_100))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.54/1.86  tff(c_310, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_283])).
% 4.54/1.86  tff(c_195, plain, (![A_90, B_91]: (r1_xboole_0(k3_xboole_0(A_90, B_91), k5_xboole_0(A_90, B_91)))), inference(cnfTransformation, [status(thm)], [f_53])).
% 4.54/1.86  tff(c_210, plain, (![A_3]: (r1_xboole_0(A_3, k5_xboole_0(A_3, A_3)))), inference(superposition, [status(thm), theory('equality')], [c_4, c_195])).
% 4.54/1.86  tff(c_314, plain, (![A_3]: (r1_xboole_0(A_3, k4_xboole_0(A_3, A_3)))), inference(demodulation, [status(thm), theory('equality')], [c_310, c_210])).
% 4.54/1.86  tff(c_10, plain, (![A_10]: (r2_hidden('#skF_2'(A_10), A_10) | k1_xboole_0=A_10)), inference(cnfTransformation, [status(thm)], [f_51])).
% 4.54/1.86  tff(c_368, plain, (![A_104, B_105, C_106]: (~r1_xboole_0(A_104, B_105) | ~r2_hidden(C_106, k3_xboole_0(A_104, B_105)))), inference(cnfTransformation, [status(thm)], [f_43])).
% 4.54/1.86  tff(c_401, plain, (![A_110, B_111]: (~r1_xboole_0(A_110, B_111) | k3_xboole_0(A_110, B_111)=k1_xboole_0)), inference(resolution, [status(thm)], [c_10, c_368])).
% 4.54/1.86  tff(c_424, plain, (![A_3]: (k3_xboole_0(A_3, k4_xboole_0(A_3, A_3))=k1_xboole_0)), inference(resolution, [status(thm)], [c_314, c_401])).
% 4.54/1.86  tff(c_431, plain, (![A_112]: (k3_xboole_0(A_112, k4_xboole_0(A_112, A_112))=k1_xboole_0)), inference(resolution, [status(thm)], [c_314, c_401])).
% 4.54/1.86  tff(c_14, plain, (![A_14, B_15]: (k5_xboole_0(A_14, k3_xboole_0(A_14, B_15))=k4_xboole_0(A_14, B_15))), inference(cnfTransformation, [status(thm)], [f_55])).
% 4.54/1.86  tff(c_439, plain, (![A_112]: (k4_xboole_0(A_112, k4_xboole_0(A_112, A_112))=k5_xboole_0(A_112, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_431, c_14])).
% 4.54/1.86  tff(c_458, plain, (![A_112]: (k4_xboole_0(A_112, k4_xboole_0(A_112, A_112))=A_112)), inference(demodulation, [status(thm), theory('equality')], [c_18, c_439])).
% 4.54/1.86  tff(c_949, plain, (![A_127, B_128]: (k4_xboole_0(A_127, k4_xboole_0(A_127, B_128))=k3_xboole_0(A_127, B_128))), inference(cnfTransformation, [status(thm)], [f_57])).
% 4.54/1.86  tff(c_974, plain, (![A_112]: (k3_xboole_0(A_112, k4_xboole_0(A_112, A_112))=k4_xboole_0(A_112, A_112))), inference(superposition, [status(thm), theory('equality')], [c_458, c_949])).
% 4.54/1.86  tff(c_985, plain, (![A_112]: (k4_xboole_0(A_112, A_112)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_424, c_974])).
% 4.54/1.86  tff(c_992, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_985, c_310])).
% 4.54/1.86  tff(c_78, plain, (k3_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_tarski('#skF_7')), inference(cnfTransformation, [status(thm)], [f_106])).
% 4.54/1.86  tff(c_301, plain, (k5_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_7'))=k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_78, c_283])).
% 4.54/1.86  tff(c_1076, plain, (k4_xboole_0(k1_tarski('#skF_7'), k1_tarski('#skF_8'))=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_992, c_301])).
% 4.54/1.86  tff(c_20, plain, (![A_19, B_20]: (k5_xboole_0(A_19, k4_xboole_0(B_20, A_19))=k2_xboole_0(A_19, B_20))), inference(cnfTransformation, [status(thm)], [f_61])).
% 4.54/1.86  tff(c_1268, plain, (k2_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k5_xboole_0(k1_tarski('#skF_8'), k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_1076, c_20])).
% 4.54/1.86  tff(c_1272, plain, (k2_xboole_0(k1_tarski('#skF_8'), k1_tarski('#skF_7'))=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_18, c_1268])).
% 4.54/1.86  tff(c_3953, plain, (k2_tarski('#skF_8', '#skF_7')=k1_tarski('#skF_8')), inference(superposition, [status(thm), theory('equality')], [c_3941, c_1272])).
% 4.54/1.86  tff(c_171, plain, (![A_86, B_87]: (k1_enumset1(A_86, A_86, B_87)=k2_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_91])).
% 4.54/1.86  tff(c_24, plain, (![E_27, A_21, B_22]: (r2_hidden(E_27, k1_enumset1(A_21, B_22, E_27)))), inference(cnfTransformation, [status(thm)], [f_76])).
% 4.54/1.86  tff(c_183, plain, (![B_87, A_86]: (r2_hidden(B_87, k2_tarski(A_86, B_87)))), inference(superposition, [status(thm), theory('equality')], [c_171, c_24])).
% 4.54/1.86  tff(c_3978, plain, (r2_hidden('#skF_7', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_3953, c_183])).
% 4.54/1.86  tff(c_46, plain, (![C_32, A_28]: (C_32=A_28 | ~r2_hidden(C_32, k1_tarski(A_28)))), inference(cnfTransformation, [status(thm)], [f_83])).
% 4.54/1.86  tff(c_4057, plain, ('#skF_7'='#skF_8'), inference(resolution, [status(thm)], [c_3978, c_46])).
% 4.54/1.86  tff(c_4061, plain, $false, inference(negUnitSimplification, [status(thm)], [c_76, c_4057])).
% 4.54/1.86  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 4.54/1.86  
% 4.54/1.86  Inference rules
% 4.54/1.86  ----------------------
% 4.54/1.86  #Ref     : 0
% 4.54/1.86  #Sup     : 957
% 4.54/1.86  #Fact    : 0
% 4.54/1.86  #Define  : 0
% 4.54/1.86  #Split   : 2
% 4.54/1.86  #Chain   : 0
% 4.54/1.86  #Close   : 0
% 4.54/1.86  
% 4.54/1.86  Ordering : KBO
% 4.54/1.86  
% 4.54/1.86  Simplification rules
% 4.54/1.86  ----------------------
% 4.54/1.86  #Subsume      : 54
% 4.54/1.86  #Demod        : 1004
% 4.54/1.86  #Tautology    : 718
% 4.54/1.86  #SimpNegUnit  : 33
% 4.54/1.86  #BackRed      : 19
% 4.54/1.86  
% 4.54/1.86  #Partial instantiations: 0
% 4.54/1.86  #Strategies tried      : 1
% 4.54/1.86  
% 4.54/1.86  Timing (in seconds)
% 4.54/1.86  ----------------------
% 4.54/1.86  Preprocessing        : 0.34
% 4.54/1.86  Parsing              : 0.17
% 4.54/1.86  CNF conversion       : 0.03
% 4.54/1.87  Main loop            : 0.75
% 4.54/1.87  Inferencing          : 0.23
% 4.54/1.87  Reduction            : 0.33
% 4.54/1.87  Demodulation         : 0.27
% 4.54/1.87  BG Simplification    : 0.03
% 4.54/1.87  Subsumption          : 0.11
% 4.54/1.87  Abstraction          : 0.04
% 4.54/1.87  MUC search           : 0.00
% 4.54/1.87  Cooper               : 0.00
% 4.54/1.87  Total                : 1.12
% 4.54/1.87  Index Insertion      : 0.00
% 4.54/1.87  Index Deletion       : 0.00
% 4.54/1.87  Index Matching       : 0.00
% 4.54/1.87  BG Taut test         : 0.00
%------------------------------------------------------------------------------

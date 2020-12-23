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
% DateTime   : Thu Dec  3 09:49:02 EST 2020

% Result     : Theorem 7.11s
% Output     : CNFRefutation 7.22s
% Verified   : 
% Statistics : Number of formulae       :   88 ( 115 expanded)
%              Number of leaves         :   41 (  55 expanded)
%              Depth                    :   13
%              Number of atoms          :   85 ( 124 expanded)
%              Number of equality atoms :   70 ( 101 expanded)
%              Maximal formula depth    :   12 (   4 average)
%              Maximal term depth       :    4 (   2 average)

% Comments   : 
%------------------------------------------------------------------------------
%$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1

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

tff('#skF_5',type,(
    '#skF_5': $i )).

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

tff(f_92,negated_conjecture,(
    ~ ! [A,B,C] :
        ~ ( r1_tarski(k1_tarski(A),k2_tarski(B,C))
          & A != B
          & A != C ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t25_zfmisc_1)).

tff(f_72,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_70,axiom,(
    ! [A,B] : k1_enumset1(A,A,B) = k2_tarski(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t70_enumset1)).

tff(f_74,axiom,(
    ! [A,B,C,D] : k3_enumset1(A,A,B,C,D) = k2_enumset1(A,B,C,D) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t72_enumset1)).

tff(f_76,axiom,(
    ! [A,B,C,D,E] : k4_enumset1(A,A,B,C,D,E) = k3_enumset1(A,B,C,D,E) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t73_enumset1)).

tff(f_78,axiom,(
    ! [A,B,C,D,E,F] : k5_enumset1(A,A,B,C,D,E,F) = k4_enumset1(A,B,C,D,E,F) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t74_enumset1)).

tff(f_66,axiom,(
    ! [A,B,C,D,E,F,G] : k5_enumset1(A,B,C,D,E,F,G) = k2_xboole_0(k4_enumset1(A,B,C,D,E,F),k1_tarski(G)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t61_enumset1)).

tff(f_45,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_27,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_33,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_41,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_31,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_43,axiom,(
    ! [A,B] : k4_xboole_0(A,k4_xboole_0(A,B)) = k3_xboole_0(A,B) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t48_xboole_1)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,A) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',idempotence_k3_xboole_0)).

tff(f_37,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_47,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_62,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(f_64,axiom,(
    ! [A,B,C] : k1_enumset1(A,B,C) = k1_enumset1(C,B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t102_enumset1)).

tff(c_64,plain,(
    '#skF_5' != '#skF_3' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_66,plain,(
    '#skF_3' != '#skF_4' ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_52,plain,(
    ! [A_37,B_38,C_39] : k2_enumset1(A_37,A_37,B_38,C_39) = k1_enumset1(A_37,B_38,C_39) ),
    inference(cnfTransformation,[status(thm)],[f_72])).

tff(c_50,plain,(
    ! [A_35,B_36] : k1_enumset1(A_35,A_35,B_36) = k2_tarski(A_35,B_36) ),
    inference(cnfTransformation,[status(thm)],[f_70])).

tff(c_54,plain,(
    ! [A_40,B_41,C_42,D_43] : k3_enumset1(A_40,A_40,B_41,C_42,D_43) = k2_enumset1(A_40,B_41,C_42,D_43) ),
    inference(cnfTransformation,[status(thm)],[f_74])).

tff(c_56,plain,(
    ! [C_46,E_48,A_44,B_45,D_47] : k4_enumset1(A_44,A_44,B_45,C_46,D_47,E_48) = k3_enumset1(A_44,B_45,C_46,D_47,E_48) ),
    inference(cnfTransformation,[status(thm)],[f_76])).

tff(c_58,plain,(
    ! [D_52,C_51,F_54,B_50,A_49,E_53] : k5_enumset1(A_49,A_49,B_50,C_51,D_52,E_53,F_54) = k4_enumset1(A_49,B_50,C_51,D_52,E_53,F_54) ),
    inference(cnfTransformation,[status(thm)],[f_78])).

tff(c_2797,plain,(
    ! [C_187,D_188,B_190,A_192,E_189,F_186,G_191] : k2_xboole_0(k4_enumset1(A_192,B_190,C_187,D_188,E_189,F_186),k1_tarski(G_191)) = k5_enumset1(A_192,B_190,C_187,D_188,E_189,F_186,G_191) ),
    inference(cnfTransformation,[status(thm)],[f_66])).

tff(c_2806,plain,(
    ! [C_46,E_48,A_44,B_45,D_47,G_191] : k5_enumset1(A_44,A_44,B_45,C_46,D_47,E_48,G_191) = k2_xboole_0(k3_enumset1(A_44,B_45,C_46,D_47,E_48),k1_tarski(G_191)) ),
    inference(superposition,[status(thm),theory(equality)],[c_56,c_2797])).

tff(c_5886,plain,(
    ! [B_279,C_278,E_275,A_280,D_277,G_276] : k2_xboole_0(k3_enumset1(A_280,B_279,C_278,D_277,E_275),k1_tarski(G_276)) = k4_enumset1(A_280,B_279,C_278,D_277,E_275,G_276) ),
    inference(demodulation,[status(thm),theory(equality)],[c_58,c_2806])).

tff(c_5895,plain,(
    ! [C_42,A_40,D_43,B_41,G_276] : k4_enumset1(A_40,A_40,B_41,C_42,D_43,G_276) = k2_xboole_0(k2_enumset1(A_40,B_41,C_42,D_43),k1_tarski(G_276)) ),
    inference(superposition,[status(thm),theory(equality)],[c_54,c_5886])).

tff(c_6977,plain,(
    ! [G_316,C_315,B_317,D_314,A_313] : k2_xboole_0(k2_enumset1(A_313,B_317,C_315,D_314),k1_tarski(G_316)) = k3_enumset1(A_313,B_317,C_315,D_314,G_316) ),
    inference(demodulation,[status(thm),theory(equality)],[c_56,c_5895])).

tff(c_6986,plain,(
    ! [A_37,B_38,C_39,G_316] : k3_enumset1(A_37,A_37,B_38,C_39,G_316) = k2_xboole_0(k1_enumset1(A_37,B_38,C_39),k1_tarski(G_316)) ),
    inference(superposition,[status(thm),theory(equality)],[c_52,c_6977])).

tff(c_6993,plain,(
    ! [A_318,B_319,C_320,G_321] : k2_xboole_0(k1_enumset1(A_318,B_319,C_320),k1_tarski(G_321)) = k2_enumset1(A_318,B_319,C_320,G_321) ),
    inference(demodulation,[status(thm),theory(equality)],[c_54,c_6986])).

tff(c_7032,plain,(
    ! [A_35,B_36,G_321] : k2_xboole_0(k2_tarski(A_35,B_36),k1_tarski(G_321)) = k2_enumset1(A_35,A_35,B_36,G_321) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_6993])).

tff(c_7036,plain,(
    ! [A_322,B_323,G_324] : k2_xboole_0(k2_tarski(A_322,B_323),k1_tarski(G_324)) = k1_enumset1(A_322,B_323,G_324) ),
    inference(demodulation,[status(thm),theory(equality)],[c_52,c_7032])).

tff(c_16,plain,(
    ! [A_14] : k5_xboole_0(A_14,k1_xboole_0) = A_14 ),
    inference(cnfTransformation,[status(thm)],[f_45])).

tff(c_136,plain,(
    ! [B_79,A_80] : k3_xboole_0(B_79,A_80) = k3_xboole_0(A_80,B_79) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_97,plain,(
    ! [A_69,B_70] : r1_tarski(k3_xboole_0(A_69,B_70),A_69) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_12,plain,(
    ! [A_11] :
      ( k1_xboole_0 = A_11
      | ~ r1_tarski(A_11,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_41])).

tff(c_105,plain,(
    ! [B_70] : k3_xboole_0(k1_xboole_0,B_70) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_97,c_12])).

tff(c_152,plain,(
    ! [B_79] : k3_xboole_0(B_79,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_136,c_105])).

tff(c_461,plain,(
    ! [A_102,B_103] : k5_xboole_0(A_102,k3_xboole_0(A_102,B_103)) = k4_xboole_0(A_102,B_103) ),
    inference(cnfTransformation,[status(thm)],[f_31])).

tff(c_473,plain,(
    ! [B_79] : k5_xboole_0(B_79,k1_xboole_0) = k4_xboole_0(B_79,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_152,c_461])).

tff(c_488,plain,(
    ! [B_79] : k4_xboole_0(B_79,k1_xboole_0) = B_79 ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_473])).

tff(c_725,plain,(
    ! [A_115,B_116] : k4_xboole_0(A_115,k4_xboole_0(A_115,B_116)) = k3_xboole_0(A_115,B_116) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_750,plain,(
    ! [B_79] : k4_xboole_0(B_79,B_79) = k3_xboole_0(B_79,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_488,c_725])).

tff(c_762,plain,(
    ! [B_79] : k4_xboole_0(B_79,B_79) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_152,c_750])).

tff(c_4,plain,(
    ! [A_3] : k3_xboole_0(A_3,A_3) = A_3 ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_485,plain,(
    ! [A_3] : k5_xboole_0(A_3,A_3) = k4_xboole_0(A_3,A_3) ),
    inference(superposition,[status(thm),theory(equality)],[c_4,c_461])).

tff(c_68,plain,(
    r1_tarski(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(cnfTransformation,[status(thm)],[f_92])).

tff(c_246,plain,(
    ! [A_86,B_87] :
      ( k3_xboole_0(A_86,B_87) = A_86
      | ~ r1_tarski(A_86,B_87) ) ),
    inference(cnfTransformation,[status(thm)],[f_37])).

tff(c_261,plain,(
    k3_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k1_tarski('#skF_3') ),
    inference(resolution,[status(thm)],[c_68,c_246])).

tff(c_470,plain,(
    k5_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) = k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_261,c_461])).

tff(c_689,plain,(
    k4_xboole_0(k1_tarski('#skF_3'),k2_tarski('#skF_4','#skF_5')) = k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3')) ),
    inference(demodulation,[status(thm),theory(equality)],[c_485,c_470])).

tff(c_697,plain,(
    ! [A_112,B_113] : k5_xboole_0(A_112,k4_xboole_0(B_113,A_112)) = k2_xboole_0(A_112,B_113) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_706,plain,(
    k5_xboole_0(k2_tarski('#skF_4','#skF_5'),k4_xboole_0(k1_tarski('#skF_3'),k1_tarski('#skF_3'))) = k2_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_3')) ),
    inference(superposition,[status(thm),theory(equality)],[c_689,c_697])).

tff(c_1222,plain,(
    k2_xboole_0(k2_tarski('#skF_4','#skF_5'),k1_tarski('#skF_3')) = k2_tarski('#skF_4','#skF_5') ),
    inference(demodulation,[status(thm),theory(equality)],[c_16,c_762,c_706])).

tff(c_7042,plain,(
    k1_enumset1('#skF_4','#skF_5','#skF_3') = k2_tarski('#skF_4','#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_7036,c_1222])).

tff(c_22,plain,(
    ! [E_23,A_17,B_18] : r2_hidden(E_23,k1_enumset1(A_17,B_18,E_23)) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_7099,plain,(
    r2_hidden('#skF_3',k2_tarski('#skF_4','#skF_5')) ),
    inference(superposition,[status(thm),theory(equality)],[c_7042,c_22])).

tff(c_44,plain,(
    ! [C_26,B_25,A_24] : k1_enumset1(C_26,B_25,A_24) = k1_enumset1(A_24,B_25,C_26) ),
    inference(cnfTransformation,[status(thm)],[f_64])).

tff(c_1622,plain,(
    ! [E_148,C_149,B_150,A_151] :
      ( E_148 = C_149
      | E_148 = B_150
      | E_148 = A_151
      | ~ r2_hidden(E_148,k1_enumset1(A_151,B_150,C_149)) ) ),
    inference(cnfTransformation,[status(thm)],[f_62])).

tff(c_5231,plain,(
    ! [E_262,C_263,B_264,A_265] :
      ( E_262 = C_263
      | E_262 = B_264
      | E_262 = A_265
      | ~ r2_hidden(E_262,k1_enumset1(C_263,B_264,A_265)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_44,c_1622])).

tff(c_5272,plain,(
    ! [E_262,A_35,B_36] :
      ( E_262 = A_35
      | E_262 = A_35
      | E_262 = B_36
      | ~ r2_hidden(E_262,k2_tarski(A_35,B_36)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_50,c_5231])).

tff(c_7120,plain,
    ( '#skF_3' = '#skF_4'
    | '#skF_5' = '#skF_3' ),
    inference(resolution,[status(thm)],[c_7099,c_5272])).

tff(c_7127,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_64,c_66,c_66,c_7120])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.07/0.12  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.07/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.34  % Computer   : n022.cluster.edu
% 0.13/0.34  % Model      : x86_64 x86_64
% 0.13/0.34  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.34  % Memory     : 8042.1875MB
% 0.13/0.34  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.34  % CPULimit   : 60
% 0.13/0.34  % DateTime   : Tue Dec  1 17:22:55 EST 2020
% 0.13/0.34  % CPUTime    : 
% 0.13/0.34  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 7.11/2.67  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.11/2.67  
% 7.11/2.67  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.11/2.68  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_5 > #skF_2 > #skF_3 > #skF_4 > #skF_1
% 7.11/2.68  
% 7.11/2.68  %Foreground sorts:
% 7.11/2.68  
% 7.11/2.68  
% 7.11/2.68  %Background operators:
% 7.11/2.68  
% 7.11/2.68  
% 7.11/2.68  %Foreground operators:
% 7.11/2.68  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 7.11/2.68  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 7.11/2.68  tff(k1_tarski, type, k1_tarski: $i > $i).
% 7.11/2.68  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 7.11/2.68  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 7.11/2.68  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 7.11/2.68  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 7.11/2.68  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 7.11/2.68  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 7.11/2.68  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 7.11/2.68  tff('#skF_5', type, '#skF_5': $i).
% 7.11/2.68  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 7.11/2.68  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 7.11/2.68  tff('#skF_3', type, '#skF_3': $i).
% 7.11/2.68  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 7.11/2.68  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 7.11/2.68  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 7.11/2.68  tff('#skF_4', type, '#skF_4': $i).
% 7.11/2.68  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 7.11/2.68  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 7.11/2.68  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 7.11/2.68  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 7.11/2.68  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 7.11/2.68  
% 7.22/2.69  tff(f_92, negated_conjecture, ~(![A, B, C]: ~((r1_tarski(k1_tarski(A), k2_tarski(B, C)) & ~(A = B)) & ~(A = C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t25_zfmisc_1)).
% 7.22/2.69  tff(f_72, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 7.22/2.69  tff(f_70, axiom, (![A, B]: (k1_enumset1(A, A, B) = k2_tarski(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t70_enumset1)).
% 7.22/2.69  tff(f_74, axiom, (![A, B, C, D]: (k3_enumset1(A, A, B, C, D) = k2_enumset1(A, B, C, D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t72_enumset1)).
% 7.22/2.69  tff(f_76, axiom, (![A, B, C, D, E]: (k4_enumset1(A, A, B, C, D, E) = k3_enumset1(A, B, C, D, E))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t73_enumset1)).
% 7.22/2.69  tff(f_78, axiom, (![A, B, C, D, E, F]: (k5_enumset1(A, A, B, C, D, E, F) = k4_enumset1(A, B, C, D, E, F))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t74_enumset1)).
% 7.22/2.69  tff(f_66, axiom, (![A, B, C, D, E, F, G]: (k5_enumset1(A, B, C, D, E, F, G) = k2_xboole_0(k4_enumset1(A, B, C, D, E, F), k1_tarski(G)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t61_enumset1)).
% 7.22/2.69  tff(f_45, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 7.22/2.69  tff(f_27, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 7.22/2.69  tff(f_33, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 7.22/2.69  tff(f_41, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 7.22/2.69  tff(f_31, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 7.22/2.69  tff(f_43, axiom, (![A, B]: (k4_xboole_0(A, k4_xboole_0(A, B)) = k3_xboole_0(A, B))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t48_xboole_1)).
% 7.22/2.69  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, A) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', idempotence_k3_xboole_0)).
% 7.22/2.69  tff(f_37, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 7.22/2.69  tff(f_47, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 7.22/2.69  tff(f_62, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 7.22/2.69  tff(f_64, axiom, (![A, B, C]: (k1_enumset1(A, B, C) = k1_enumset1(C, B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t102_enumset1)).
% 7.22/2.69  tff(c_64, plain, ('#skF_5'!='#skF_3'), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.22/2.69  tff(c_66, plain, ('#skF_3'!='#skF_4'), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.22/2.69  tff(c_52, plain, (![A_37, B_38, C_39]: (k2_enumset1(A_37, A_37, B_38, C_39)=k1_enumset1(A_37, B_38, C_39))), inference(cnfTransformation, [status(thm)], [f_72])).
% 7.22/2.69  tff(c_50, plain, (![A_35, B_36]: (k1_enumset1(A_35, A_35, B_36)=k2_tarski(A_35, B_36))), inference(cnfTransformation, [status(thm)], [f_70])).
% 7.22/2.69  tff(c_54, plain, (![A_40, B_41, C_42, D_43]: (k3_enumset1(A_40, A_40, B_41, C_42, D_43)=k2_enumset1(A_40, B_41, C_42, D_43))), inference(cnfTransformation, [status(thm)], [f_74])).
% 7.22/2.69  tff(c_56, plain, (![C_46, E_48, A_44, B_45, D_47]: (k4_enumset1(A_44, A_44, B_45, C_46, D_47, E_48)=k3_enumset1(A_44, B_45, C_46, D_47, E_48))), inference(cnfTransformation, [status(thm)], [f_76])).
% 7.22/2.69  tff(c_58, plain, (![D_52, C_51, F_54, B_50, A_49, E_53]: (k5_enumset1(A_49, A_49, B_50, C_51, D_52, E_53, F_54)=k4_enumset1(A_49, B_50, C_51, D_52, E_53, F_54))), inference(cnfTransformation, [status(thm)], [f_78])).
% 7.22/2.69  tff(c_2797, plain, (![C_187, D_188, B_190, A_192, E_189, F_186, G_191]: (k2_xboole_0(k4_enumset1(A_192, B_190, C_187, D_188, E_189, F_186), k1_tarski(G_191))=k5_enumset1(A_192, B_190, C_187, D_188, E_189, F_186, G_191))), inference(cnfTransformation, [status(thm)], [f_66])).
% 7.22/2.69  tff(c_2806, plain, (![C_46, E_48, A_44, B_45, D_47, G_191]: (k5_enumset1(A_44, A_44, B_45, C_46, D_47, E_48, G_191)=k2_xboole_0(k3_enumset1(A_44, B_45, C_46, D_47, E_48), k1_tarski(G_191)))), inference(superposition, [status(thm), theory('equality')], [c_56, c_2797])).
% 7.22/2.69  tff(c_5886, plain, (![B_279, C_278, E_275, A_280, D_277, G_276]: (k2_xboole_0(k3_enumset1(A_280, B_279, C_278, D_277, E_275), k1_tarski(G_276))=k4_enumset1(A_280, B_279, C_278, D_277, E_275, G_276))), inference(demodulation, [status(thm), theory('equality')], [c_58, c_2806])).
% 7.22/2.69  tff(c_5895, plain, (![C_42, A_40, D_43, B_41, G_276]: (k4_enumset1(A_40, A_40, B_41, C_42, D_43, G_276)=k2_xboole_0(k2_enumset1(A_40, B_41, C_42, D_43), k1_tarski(G_276)))), inference(superposition, [status(thm), theory('equality')], [c_54, c_5886])).
% 7.22/2.69  tff(c_6977, plain, (![G_316, C_315, B_317, D_314, A_313]: (k2_xboole_0(k2_enumset1(A_313, B_317, C_315, D_314), k1_tarski(G_316))=k3_enumset1(A_313, B_317, C_315, D_314, G_316))), inference(demodulation, [status(thm), theory('equality')], [c_56, c_5895])).
% 7.22/2.69  tff(c_6986, plain, (![A_37, B_38, C_39, G_316]: (k3_enumset1(A_37, A_37, B_38, C_39, G_316)=k2_xboole_0(k1_enumset1(A_37, B_38, C_39), k1_tarski(G_316)))), inference(superposition, [status(thm), theory('equality')], [c_52, c_6977])).
% 7.22/2.69  tff(c_6993, plain, (![A_318, B_319, C_320, G_321]: (k2_xboole_0(k1_enumset1(A_318, B_319, C_320), k1_tarski(G_321))=k2_enumset1(A_318, B_319, C_320, G_321))), inference(demodulation, [status(thm), theory('equality')], [c_54, c_6986])).
% 7.22/2.69  tff(c_7032, plain, (![A_35, B_36, G_321]: (k2_xboole_0(k2_tarski(A_35, B_36), k1_tarski(G_321))=k2_enumset1(A_35, A_35, B_36, G_321))), inference(superposition, [status(thm), theory('equality')], [c_50, c_6993])).
% 7.22/2.69  tff(c_7036, plain, (![A_322, B_323, G_324]: (k2_xboole_0(k2_tarski(A_322, B_323), k1_tarski(G_324))=k1_enumset1(A_322, B_323, G_324))), inference(demodulation, [status(thm), theory('equality')], [c_52, c_7032])).
% 7.22/2.69  tff(c_16, plain, (![A_14]: (k5_xboole_0(A_14, k1_xboole_0)=A_14)), inference(cnfTransformation, [status(thm)], [f_45])).
% 7.22/2.69  tff(c_136, plain, (![B_79, A_80]: (k3_xboole_0(B_79, A_80)=k3_xboole_0(A_80, B_79))), inference(cnfTransformation, [status(thm)], [f_27])).
% 7.22/2.69  tff(c_97, plain, (![A_69, B_70]: (r1_tarski(k3_xboole_0(A_69, B_70), A_69))), inference(cnfTransformation, [status(thm)], [f_33])).
% 7.22/2.69  tff(c_12, plain, (![A_11]: (k1_xboole_0=A_11 | ~r1_tarski(A_11, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_41])).
% 7.22/2.69  tff(c_105, plain, (![B_70]: (k3_xboole_0(k1_xboole_0, B_70)=k1_xboole_0)), inference(resolution, [status(thm)], [c_97, c_12])).
% 7.22/2.69  tff(c_152, plain, (![B_79]: (k3_xboole_0(B_79, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_136, c_105])).
% 7.22/2.69  tff(c_461, plain, (![A_102, B_103]: (k5_xboole_0(A_102, k3_xboole_0(A_102, B_103))=k4_xboole_0(A_102, B_103))), inference(cnfTransformation, [status(thm)], [f_31])).
% 7.22/2.69  tff(c_473, plain, (![B_79]: (k5_xboole_0(B_79, k1_xboole_0)=k4_xboole_0(B_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_152, c_461])).
% 7.22/2.69  tff(c_488, plain, (![B_79]: (k4_xboole_0(B_79, k1_xboole_0)=B_79)), inference(demodulation, [status(thm), theory('equality')], [c_16, c_473])).
% 7.22/2.69  tff(c_725, plain, (![A_115, B_116]: (k4_xboole_0(A_115, k4_xboole_0(A_115, B_116))=k3_xboole_0(A_115, B_116))), inference(cnfTransformation, [status(thm)], [f_43])).
% 7.22/2.69  tff(c_750, plain, (![B_79]: (k4_xboole_0(B_79, B_79)=k3_xboole_0(B_79, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_488, c_725])).
% 7.22/2.69  tff(c_762, plain, (![B_79]: (k4_xboole_0(B_79, B_79)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_152, c_750])).
% 7.22/2.69  tff(c_4, plain, (![A_3]: (k3_xboole_0(A_3, A_3)=A_3)), inference(cnfTransformation, [status(thm)], [f_29])).
% 7.22/2.69  tff(c_485, plain, (![A_3]: (k5_xboole_0(A_3, A_3)=k4_xboole_0(A_3, A_3))), inference(superposition, [status(thm), theory('equality')], [c_4, c_461])).
% 7.22/2.69  tff(c_68, plain, (r1_tarski(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(cnfTransformation, [status(thm)], [f_92])).
% 7.22/2.69  tff(c_246, plain, (![A_86, B_87]: (k3_xboole_0(A_86, B_87)=A_86 | ~r1_tarski(A_86, B_87))), inference(cnfTransformation, [status(thm)], [f_37])).
% 7.22/2.69  tff(c_261, plain, (k3_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k1_tarski('#skF_3')), inference(resolution, [status(thm)], [c_68, c_246])).
% 7.22/2.69  tff(c_470, plain, (k5_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))=k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_261, c_461])).
% 7.22/2.69  tff(c_689, plain, (k4_xboole_0(k1_tarski('#skF_3'), k2_tarski('#skF_4', '#skF_5'))=k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3'))), inference(demodulation, [status(thm), theory('equality')], [c_485, c_470])).
% 7.22/2.69  tff(c_697, plain, (![A_112, B_113]: (k5_xboole_0(A_112, k4_xboole_0(B_113, A_112))=k2_xboole_0(A_112, B_113))), inference(cnfTransformation, [status(thm)], [f_47])).
% 7.22/2.69  tff(c_706, plain, (k5_xboole_0(k2_tarski('#skF_4', '#skF_5'), k4_xboole_0(k1_tarski('#skF_3'), k1_tarski('#skF_3')))=k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_3'))), inference(superposition, [status(thm), theory('equality')], [c_689, c_697])).
% 7.22/2.69  tff(c_1222, plain, (k2_xboole_0(k2_tarski('#skF_4', '#skF_5'), k1_tarski('#skF_3'))=k2_tarski('#skF_4', '#skF_5')), inference(demodulation, [status(thm), theory('equality')], [c_16, c_762, c_706])).
% 7.22/2.69  tff(c_7042, plain, (k1_enumset1('#skF_4', '#skF_5', '#skF_3')=k2_tarski('#skF_4', '#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_7036, c_1222])).
% 7.22/2.69  tff(c_22, plain, (![E_23, A_17, B_18]: (r2_hidden(E_23, k1_enumset1(A_17, B_18, E_23)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.22/2.69  tff(c_7099, plain, (r2_hidden('#skF_3', k2_tarski('#skF_4', '#skF_5'))), inference(superposition, [status(thm), theory('equality')], [c_7042, c_22])).
% 7.22/2.69  tff(c_44, plain, (![C_26, B_25, A_24]: (k1_enumset1(C_26, B_25, A_24)=k1_enumset1(A_24, B_25, C_26))), inference(cnfTransformation, [status(thm)], [f_64])).
% 7.22/2.69  tff(c_1622, plain, (![E_148, C_149, B_150, A_151]: (E_148=C_149 | E_148=B_150 | E_148=A_151 | ~r2_hidden(E_148, k1_enumset1(A_151, B_150, C_149)))), inference(cnfTransformation, [status(thm)], [f_62])).
% 7.22/2.69  tff(c_5231, plain, (![E_262, C_263, B_264, A_265]: (E_262=C_263 | E_262=B_264 | E_262=A_265 | ~r2_hidden(E_262, k1_enumset1(C_263, B_264, A_265)))), inference(superposition, [status(thm), theory('equality')], [c_44, c_1622])).
% 7.22/2.69  tff(c_5272, plain, (![E_262, A_35, B_36]: (E_262=A_35 | E_262=A_35 | E_262=B_36 | ~r2_hidden(E_262, k2_tarski(A_35, B_36)))), inference(superposition, [status(thm), theory('equality')], [c_50, c_5231])).
% 7.22/2.69  tff(c_7120, plain, ('#skF_3'='#skF_4' | '#skF_5'='#skF_3'), inference(resolution, [status(thm)], [c_7099, c_5272])).
% 7.22/2.69  tff(c_7127, plain, $false, inference(negUnitSimplification, [status(thm)], [c_64, c_66, c_66, c_7120])).
% 7.22/2.69  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 7.22/2.69  
% 7.22/2.69  Inference rules
% 7.22/2.69  ----------------------
% 7.22/2.69  #Ref     : 0
% 7.22/2.69  #Sup     : 1738
% 7.22/2.69  #Fact    : 6
% 7.22/2.69  #Define  : 0
% 7.22/2.69  #Split   : 0
% 7.22/2.69  #Chain   : 0
% 7.22/2.69  #Close   : 0
% 7.22/2.69  
% 7.22/2.69  Ordering : KBO
% 7.22/2.69  
% 7.22/2.69  Simplification rules
% 7.22/2.69  ----------------------
% 7.22/2.69  #Subsume      : 239
% 7.22/2.69  #Demod        : 2607
% 7.22/2.69  #Tautology    : 1306
% 7.22/2.69  #SimpNegUnit  : 1
% 7.22/2.69  #BackRed      : 2
% 7.22/2.69  
% 7.22/2.69  #Partial instantiations: 0
% 7.22/2.69  #Strategies tried      : 1
% 7.22/2.69  
% 7.22/2.69  Timing (in seconds)
% 7.22/2.69  ----------------------
% 7.22/2.70  Preprocessing        : 0.43
% 7.22/2.70  Parsing              : 0.23
% 7.22/2.70  CNF conversion       : 0.03
% 7.22/2.70  Main loop            : 1.49
% 7.22/2.70  Inferencing          : 0.41
% 7.22/2.70  Reduction            : 0.74
% 7.22/2.70  Demodulation         : 0.64
% 7.22/2.70  BG Simplification    : 0.05
% 7.22/2.70  Subsumption          : 0.22
% 7.22/2.70  Abstraction          : 0.08
% 7.22/2.70  MUC search           : 0.00
% 7.22/2.70  Cooper               : 0.00
% 7.22/2.70  Total                : 1.95
% 7.22/2.70  Index Insertion      : 0.00
% 7.22/2.70  Index Deletion       : 0.00
% 7.22/2.70  Index Matching       : 0.00
% 7.22/2.70  BG Taut test         : 0.00
%------------------------------------------------------------------------------

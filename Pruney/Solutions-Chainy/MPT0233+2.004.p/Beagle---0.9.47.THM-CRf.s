%------------------------------------------------------------------------------
% File       : Beagle---0.9.47
% Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% Transform  : none
% Format     : tptp:raw
% Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s

% Computer   : n011.cluster.edu
% Model      : x86_64 x86_64
% CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 2.10GHz
% Memory     : 8042.1875MB
% OS         : Linux 3.10.0-693.el7.x86_64
% CPULimit   : 60s
% DateTime   : Thu Dec  3 09:49:24 EST 2020

% Result     : Theorem 6.00s
% Output     : CNFRefutation 6.00s
% Verified   : 
% Statistics : Number of formulae       :  110 ( 379 expanded)
%              Number of leaves         :   41 ( 139 expanded)
%              Depth                    :   14
%              Number of atoms          :  122 ( 758 expanded)
%              Number of equality atoms :   90 ( 567 expanded)
%              Maximal formula depth    :   12 (   3 average)
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

tff(f_122,negated_conjecture,(
    ~ ! [A,B,C,D] :
        ~ ( r1_tarski(k2_tarski(A,B),k2_tarski(C,D))
          & A != C
          & A != D ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_zfmisc_1)).

tff(f_83,axiom,(
    ! [A] : k2_tarski(A,A) = k1_tarski(A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t69_enumset1)).

tff(f_87,axiom,(
    ! [A,B,C] : k2_enumset1(A,A,B,C) = k1_enumset1(A,B,C) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t71_enumset1)).

tff(f_51,axiom,(
    ! [A] : k5_xboole_0(A,k1_xboole_0) = A ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t5_boole)).

tff(f_35,axiom,(
    ! [A,B] : r1_tarski(k3_xboole_0(A,B),A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t17_xboole_1)).

tff(f_47,axiom,(
    ! [A] :
      ( r1_tarski(A,k1_xboole_0)
     => A = k1_xboole_0 ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t3_xboole_1)).

tff(f_33,axiom,(
    ! [A,B] : k4_xboole_0(A,B) = k5_xboole_0(A,k3_xboole_0(A,B)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t100_xboole_1)).

tff(f_53,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k5_xboole_0(A,k4_xboole_0(B,A)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t98_xboole_1)).

tff(f_27,axiom,(
    ! [A,B] : k2_xboole_0(A,B) = k2_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k2_xboole_0)).

tff(f_112,axiom,(
    ! [A,B,C] :
      ( r1_tarski(A,k2_tarski(B,C))
    <=> ~ ( A != k1_xboole_0
          & A != k1_tarski(B)
          & A != k1_tarski(C)
          & A != k2_tarski(B,C) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l45_zfmisc_1)).

tff(f_77,axiom,(
    ! [A,B,C] :
      ( C = k2_tarski(A,B)
    <=> ! [D] :
          ( r2_hidden(D,C)
        <=> ( D = A
            | D = B ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d2_tarski)).

tff(f_29,axiom,(
    ! [A,B] : k3_xboole_0(A,B) = k3_xboole_0(B,A) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',commutativity_k3_xboole_0)).

tff(f_43,axiom,(
    ! [A,B] :
      ( r1_tarski(A,B)
     => k3_xboole_0(A,B) = A ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',t28_xboole_1)).

tff(f_79,axiom,(
    ! [A,B,C,D] : k2_enumset1(A,B,C,D) = k2_xboole_0(k2_tarski(A,B),k2_tarski(C,D)) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',l53_enumset1)).

tff(f_68,axiom,(
    ! [A,B,C,D] :
      ( D = k1_enumset1(A,B,C)
    <=> ! [E] :
          ( r2_hidden(E,D)
        <=> ~ ( E != A
              & E != B
              & E != C ) ) ) ),
    file('/export/starexec/sandbox/benchmark/theBenchmark.p',d1_enumset1)).

tff(c_96,plain,(
    '#skF_5' != '#skF_8' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_98,plain,(
    '#skF_7' != '#skF_5' ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_70,plain,(
    ! [A_43] : k2_tarski(A_43,A_43) = k1_tarski(A_43) ),
    inference(cnfTransformation,[status(thm)],[f_83])).

tff(c_74,plain,(
    ! [A_46,B_47,C_48] : k2_enumset1(A_46,A_46,B_47,C_48) = k1_enumset1(A_46,B_47,C_48) ),
    inference(cnfTransformation,[status(thm)],[f_87])).

tff(c_20,plain,(
    ! [A_19] : k5_xboole_0(A_19,k1_xboole_0) = A_19 ),
    inference(cnfTransformation,[status(thm)],[f_51])).

tff(c_143,plain,(
    ! [A_89,B_90] : r1_tarski(k3_xboole_0(A_89,B_90),A_89) ),
    inference(cnfTransformation,[status(thm)],[f_35])).

tff(c_16,plain,(
    ! [A_16] :
      ( k1_xboole_0 = A_16
      | ~ r1_tarski(A_16,k1_xboole_0) ) ),
    inference(cnfTransformation,[status(thm)],[f_47])).

tff(c_151,plain,(
    ! [B_90] : k3_xboole_0(k1_xboole_0,B_90) = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_143,c_16])).

tff(c_427,plain,(
    ! [A_120,B_121] : k5_xboole_0(A_120,k3_xboole_0(A_120,B_121)) = k4_xboole_0(A_120,B_121) ),
    inference(cnfTransformation,[status(thm)],[f_33])).

tff(c_445,plain,(
    ! [B_90] : k5_xboole_0(k1_xboole_0,k1_xboole_0) = k4_xboole_0(k1_xboole_0,B_90) ),
    inference(superposition,[status(thm),theory(equality)],[c_151,c_427])).

tff(c_453,plain,(
    ! [B_122] : k4_xboole_0(k1_xboole_0,B_122) = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_445])).

tff(c_22,plain,(
    ! [A_20,B_21] : k5_xboole_0(A_20,k4_xboole_0(B_21,A_20)) = k2_xboole_0(A_20,B_21) ),
    inference(cnfTransformation,[status(thm)],[f_53])).

tff(c_458,plain,(
    ! [B_122] : k5_xboole_0(B_122,k1_xboole_0) = k2_xboole_0(B_122,k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_453,c_22])).

tff(c_523,plain,(
    ! [B_126] : k2_xboole_0(B_126,k1_xboole_0) = B_126 ),
    inference(demodulation,[status(thm),theory(equality)],[c_20,c_458])).

tff(c_2,plain,(
    ! [B_2,A_1] : k2_xboole_0(B_2,A_1) = k2_xboole_0(A_1,B_2) ),
    inference(cnfTransformation,[status(thm)],[f_27])).

tff(c_529,plain,(
    ! [B_126] : k2_xboole_0(k1_xboole_0,B_126) = B_126 ),
    inference(superposition,[status(thm),theory(equality)],[c_523,c_2])).

tff(c_100,plain,(
    r1_tarski(k2_tarski('#skF_5','#skF_6'),k2_tarski('#skF_7','#skF_8')) ),
    inference(cnfTransformation,[status(thm)],[f_122])).

tff(c_5029,plain,(
    ! [B_273,C_274,A_275] :
      ( k2_tarski(B_273,C_274) = A_275
      | k1_tarski(C_274) = A_275
      | k1_tarski(B_273) = A_275
      | k1_xboole_0 = A_275
      | ~ r1_tarski(A_275,k2_tarski(B_273,C_274)) ) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_5124,plain,
    ( k2_tarski('#skF_7','#skF_8') = k2_tarski('#skF_5','#skF_6')
    | k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_8')
    | k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7')
    | k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(resolution,[status(thm)],[c_100,c_5029])).

tff(c_5129,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_xboole_0 ),
    inference(splitLeft,[status(thm)],[c_5124])).

tff(c_50,plain,(
    ! [D_34,A_29] : r2_hidden(D_34,k2_tarski(A_29,D_34)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5203,plain,(
    r2_hidden('#skF_6',k1_xboole_0) ),
    inference(superposition,[status(thm),theory(equality)],[c_5129,c_50])).

tff(c_185,plain,(
    ! [B_95,A_96] : k3_xboole_0(B_95,A_96) = k3_xboole_0(A_96,B_95) ),
    inference(cnfTransformation,[status(thm)],[f_29])).

tff(c_201,plain,(
    ! [B_95] : k3_xboole_0(B_95,k1_xboole_0) = k1_xboole_0 ),
    inference(superposition,[status(thm),theory(equality)],[c_185,c_151])).

tff(c_92,plain,(
    ! [B_75,C_76] : r1_tarski(k1_tarski(B_75),k2_tarski(B_75,C_76)) ),
    inference(cnfTransformation,[status(thm)],[f_112])).

tff(c_387,plain,(
    ! [A_116,B_117] :
      ( k3_xboole_0(A_116,B_117) = A_116
      | ~ r1_tarski(A_116,B_117) ) ),
    inference(cnfTransformation,[status(thm)],[f_43])).

tff(c_409,plain,(
    ! [B_75,C_76] : k3_xboole_0(k1_tarski(B_75),k2_tarski(B_75,C_76)) = k1_tarski(B_75) ),
    inference(resolution,[status(thm)],[c_92,c_387])).

tff(c_5182,plain,(
    k3_xboole_0(k1_tarski('#skF_5'),k1_xboole_0) = k1_tarski('#skF_5') ),
    inference(superposition,[status(thm),theory(equality)],[c_5129,c_409])).

tff(c_5211,plain,(
    k1_tarski('#skF_5') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_201,c_5182])).

tff(c_1213,plain,(
    ! [D_158,B_159,A_160] :
      ( D_158 = B_159
      | D_158 = A_160
      | ~ r2_hidden(D_158,k2_tarski(A_160,B_159)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_1222,plain,(
    ! [D_158,A_43] :
      ( D_158 = A_43
      | D_158 = A_43
      | ~ r2_hidden(D_158,k1_tarski(A_43)) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_70,c_1213])).

tff(c_5376,plain,(
    ! [D_285] :
      ( D_285 = '#skF_5'
      | D_285 = '#skF_5'
      | ~ r2_hidden(D_285,k1_xboole_0) ) ),
    inference(superposition,[status(thm),theory(equality)],[c_5211,c_1222])).

tff(c_5387,plain,(
    '#skF_5' = '#skF_6' ),
    inference(resolution,[status(thm)],[c_5203,c_5376])).

tff(c_5395,plain,(
    k2_tarski('#skF_6','#skF_6') = k1_xboole_0 ),
    inference(demodulation,[status(thm),theory(equality)],[c_5387,c_5129])).

tff(c_66,plain,(
    ! [A_35,B_36,C_37,D_38] : k2_xboole_0(k2_tarski(A_35,B_36),k2_tarski(C_37,D_38)) = k2_enumset1(A_35,B_36,C_37,D_38) ),
    inference(cnfTransformation,[status(thm)],[f_79])).

tff(c_5429,plain,(
    ! [C_37,D_38] : k2_xboole_0(k1_xboole_0,k2_tarski(C_37,D_38)) = k2_enumset1('#skF_6','#skF_6',C_37,D_38) ),
    inference(superposition,[status(thm),theory(equality)],[c_5395,c_66])).

tff(c_5501,plain,(
    ! [C_291,D_292] : k1_enumset1('#skF_6',C_291,D_292) = k2_tarski(C_291,D_292) ),
    inference(demodulation,[status(thm),theory(equality)],[c_74,c_529,c_5429])).

tff(c_30,plain,(
    ! [E_28,B_23,C_24] : r2_hidden(E_28,k1_enumset1(E_28,B_23,C_24)) ),
    inference(cnfTransformation,[status(thm)],[f_68])).

tff(c_5559,plain,(
    ! [C_293,D_294] : r2_hidden('#skF_6',k2_tarski(C_293,D_294)) ),
    inference(superposition,[status(thm),theory(equality)],[c_5501,c_30])).

tff(c_48,plain,(
    ! [D_34,B_30,A_29] :
      ( D_34 = B_30
      | D_34 = A_29
      | ~ r2_hidden(D_34,k2_tarski(A_29,B_30)) ) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_5567,plain,(
    ! [D_294,C_293] :
      ( D_294 = '#skF_6'
      | C_293 = '#skF_6' ) ),
    inference(resolution,[status(thm)],[c_5559,c_48])).

tff(c_5570,plain,(
    ! [C_295] : C_295 = '#skF_6' ),
    inference(splitLeft,[status(thm)],[c_5567])).

tff(c_5398,plain,(
    '#skF_7' != '#skF_6' ),
    inference(demodulation,[status(thm),theory(equality)],[c_5387,c_98])).

tff(c_5913,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_5570,c_5398])).

tff(c_5916,plain,(
    ! [D_5996] : D_5996 = '#skF_6' ),
    inference(splitRight,[status(thm)],[c_5567])).

tff(c_6261,plain,(
    $false ),
    inference(superposition,[status(thm),theory(equality)],[c_5916,c_5398])).

tff(c_6262,plain,
    ( k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7')
    | k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_8')
    | k2_tarski('#skF_7','#skF_8') = k2_tarski('#skF_5','#skF_6') ),
    inference(splitRight,[status(thm)],[c_5124])).

tff(c_6265,plain,(
    k2_tarski('#skF_7','#skF_8') = k2_tarski('#skF_5','#skF_6') ),
    inference(splitLeft,[status(thm)],[c_6262])).

tff(c_6348,plain,(
    r2_hidden('#skF_8',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6265,c_50])).

tff(c_6371,plain,
    ( '#skF_6' = '#skF_8'
    | '#skF_5' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_6348,c_48])).

tff(c_6374,plain,(
    '#skF_6' = '#skF_8' ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_6371])).

tff(c_52,plain,(
    ! [D_34,B_30] : r2_hidden(D_34,k2_tarski(D_34,B_30)) ),
    inference(cnfTransformation,[status(thm)],[f_77])).

tff(c_6345,plain,(
    r2_hidden('#skF_7',k2_tarski('#skF_5','#skF_6')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6265,c_52])).

tff(c_6357,plain,
    ( '#skF_7' = '#skF_6'
    | '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6345,c_48])).

tff(c_6360,plain,(
    '#skF_7' = '#skF_6' ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_6357])).

tff(c_6362,plain,(
    k2_tarski('#skF_5','#skF_6') = k2_tarski('#skF_6','#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_6360,c_6265])).

tff(c_6396,plain,(
    k2_tarski('#skF_5','#skF_8') = k1_tarski('#skF_8') ),
    inference(demodulation,[status(thm),theory(equality)],[c_70,c_6374,c_6374,c_6362])).

tff(c_6449,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6396,c_52])).

tff(c_6466,plain,(
    '#skF_5' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_6449,c_1222])).

tff(c_6470,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_96,c_6466])).

tff(c_6471,plain,
    ( k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_8')
    | k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7') ),
    inference(splitRight,[status(thm)],[c_6262])).

tff(c_6618,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_7') ),
    inference(splitLeft,[status(thm)],[c_6471])).

tff(c_6688,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_7')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6618,c_52])).

tff(c_6698,plain,(
    '#skF_7' = '#skF_5' ),
    inference(resolution,[status(thm)],[c_6688,c_1222])).

tff(c_6702,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_98,c_98,c_6698])).

tff(c_6703,plain,(
    k2_tarski('#skF_5','#skF_6') = k1_tarski('#skF_8') ),
    inference(splitRight,[status(thm)],[c_6471])).

tff(c_6774,plain,(
    r2_hidden('#skF_5',k1_tarski('#skF_8')) ),
    inference(superposition,[status(thm),theory(equality)],[c_6703,c_52])).

tff(c_6785,plain,(
    '#skF_5' = '#skF_8' ),
    inference(resolution,[status(thm)],[c_6774,c_1222])).

tff(c_6789,plain,(
    $false ),
    inference(negUnitSimplification,[status(thm)],[c_96,c_96,c_6785])).
%------------------------------------------------------------------------------
%----ORIGINAL SYSTEM OUTPUT
% 0.03/0.13  % Problem    : MPT0001+2.001 : TPTP v7.5.0. Released v7.5.0.
% 0.03/0.13  % Command    : java -Xms512M -Xmx4G -Xss10M -XX:MaxPermSize=384M -jar /export/starexec/sandbox/solver/bin/beagle.jar -auto -q -proof -print tff -smtsolver /export/starexec/sandbox/solver/bin/cvc4-1.4-x86_64-linux-opt -liasolver cooper -t %d %s
% 0.13/0.35  % Computer   : n011.cluster.edu
% 0.13/0.35  % Model      : x86_64 x86_64
% 0.13/0.35  % CPU        : Intel(R) Xeon(R) CPU E5-2620 v4 @ 2.10GHz
% 0.13/0.35  % Memory     : 8042.1875MB
% 0.13/0.35  % OS         : Linux 3.10.0-693.el7.x86_64
% 0.13/0.35  % CPULimit   : 60
% 0.13/0.35  % DateTime   : Tue Dec  1 20:09:27 EST 2020
% 0.13/0.35  % CPUTime    : 
% 0.13/0.35  OpenJDK 64-Bit Server VM warning: ignoring option MaxPermSize=384M; support was removed in 8.0
% 6.00/2.22  % SZS status Theorem for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.00/2.23  
% 6.00/2.23  % SZS output start CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.00/2.23  %$ r2_hidden > r1_tarski > k6_enumset1 > k5_enumset1 > k4_enumset1 > k3_enumset1 > k2_enumset1 > k1_enumset1 > k5_xboole_0 > k4_xboole_0 > k3_xboole_0 > k2_xboole_0 > k2_tarski > #nlpp > k1_tarski > k1_xboole_0 > #skF_4 > #skF_7 > #skF_5 > #skF_2 > #skF_6 > #skF_8 > #skF_3 > #skF_1
% 6.00/2.23  
% 6.00/2.23  %Foreground sorts:
% 6.00/2.23  
% 6.00/2.23  
% 6.00/2.23  %Background operators:
% 6.00/2.23  
% 6.00/2.23  
% 6.00/2.23  %Foreground operators:
% 6.00/2.23  tff('#nlpp', type, '#nlpp': ($real * $real) > $real).
% 6.00/2.23  tff(r2_hidden, type, r2_hidden: ($i * $i) > $o).
% 6.00/2.23  tff(k1_tarski, type, k1_tarski: $i > $i).
% 6.00/2.23  tff(k4_xboole_0, type, k4_xboole_0: ($i * $i) > $i).
% 6.00/2.23  tff(k1_xboole_0, type, k1_xboole_0: $i).
% 6.00/2.23  tff(k3_enumset1, type, k3_enumset1: ($i * $i * $i * $i * $i) > $i).
% 6.00/2.23  tff('#skF_4', type, '#skF_4': ($i * $i * $i) > $i).
% 6.00/2.23  tff('#skF_7', type, '#skF_7': $i).
% 6.00/2.23  tff(k5_xboole_0, type, k5_xboole_0: ($i * $i) > $i).
% 6.00/2.23  tff(r1_tarski, type, r1_tarski: ($i * $i) > $o).
% 6.00/2.23  tff(k2_enumset1, type, k2_enumset1: ($i * $i * $i * $i) > $i).
% 6.00/2.23  tff(k2_tarski, type, k2_tarski: ($i * $i) > $i).
% 6.00/2.23  tff('#skF_5', type, '#skF_5': $i).
% 6.00/2.23  tff('#skF_2', type, '#skF_2': ($i * $i * $i * $i) > $i).
% 6.00/2.23  tff('#skF_6', type, '#skF_6': $i).
% 6.00/2.23  tff(k1_enumset1, type, k1_enumset1: ($i * $i * $i) > $i).
% 6.00/2.23  tff(k4_enumset1, type, k4_enumset1: ($i * $i * $i * $i * $i * $i) > $i).
% 6.00/2.23  tff(k6_enumset1, type, k6_enumset1: ($i * $i * $i * $i * $i * $i * $i * $i) > $i).
% 6.00/2.23  tff('#skF_8', type, '#skF_8': $i).
% 6.00/2.23  tff('#nlpp', type, '#nlpp': ($rat * $rat) > $rat).
% 6.00/2.23  tff('#skF_3', type, '#skF_3': ($i * $i * $i) > $i).
% 6.00/2.23  tff('#nlpp', type, '#nlpp': ($int * $int) > $int).
% 6.00/2.23  tff(k3_xboole_0, type, k3_xboole_0: ($i * $i) > $i).
% 6.00/2.23  tff(k2_xboole_0, type, k2_xboole_0: ($i * $i) > $i).
% 6.00/2.23  tff(k5_enumset1, type, k5_enumset1: ($i * $i * $i * $i * $i * $i * $i) > $i).
% 6.00/2.23  tff('#skF_1', type, '#skF_1': ($i * $i * $i * $i) > $i).
% 6.00/2.23  
% 6.00/2.25  tff(f_122, negated_conjecture, ~(![A, B, C, D]: ~((r1_tarski(k2_tarski(A, B), k2_tarski(C, D)) & ~(A = C)) & ~(A = D))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_zfmisc_1)).
% 6.00/2.25  tff(f_83, axiom, (![A]: (k2_tarski(A, A) = k1_tarski(A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t69_enumset1)).
% 6.00/2.25  tff(f_87, axiom, (![A, B, C]: (k2_enumset1(A, A, B, C) = k1_enumset1(A, B, C))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t71_enumset1)).
% 6.00/2.25  tff(f_51, axiom, (![A]: (k5_xboole_0(A, k1_xboole_0) = A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t5_boole)).
% 6.00/2.25  tff(f_35, axiom, (![A, B]: r1_tarski(k3_xboole_0(A, B), A)), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t17_xboole_1)).
% 6.00/2.25  tff(f_47, axiom, (![A]: (r1_tarski(A, k1_xboole_0) => (A = k1_xboole_0))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t3_xboole_1)).
% 6.00/2.25  tff(f_33, axiom, (![A, B]: (k4_xboole_0(A, B) = k5_xboole_0(A, k3_xboole_0(A, B)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t100_xboole_1)).
% 6.00/2.25  tff(f_53, axiom, (![A, B]: (k2_xboole_0(A, B) = k5_xboole_0(A, k4_xboole_0(B, A)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t98_xboole_1)).
% 6.00/2.25  tff(f_27, axiom, (![A, B]: (k2_xboole_0(A, B) = k2_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k2_xboole_0)).
% 6.00/2.25  tff(f_112, axiom, (![A, B, C]: (r1_tarski(A, k2_tarski(B, C)) <=> ~(((~(A = k1_xboole_0) & ~(A = k1_tarski(B))) & ~(A = k1_tarski(C))) & ~(A = k2_tarski(B, C))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l45_zfmisc_1)).
% 6.00/2.25  tff(f_77, axiom, (![A, B, C]: ((C = k2_tarski(A, B)) <=> (![D]: (r2_hidden(D, C) <=> ((D = A) | (D = B)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d2_tarski)).
% 6.00/2.25  tff(f_29, axiom, (![A, B]: (k3_xboole_0(A, B) = k3_xboole_0(B, A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', commutativity_k3_xboole_0)).
% 6.00/2.25  tff(f_43, axiom, (![A, B]: (r1_tarski(A, B) => (k3_xboole_0(A, B) = A))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', t28_xboole_1)).
% 6.00/2.25  tff(f_79, axiom, (![A, B, C, D]: (k2_enumset1(A, B, C, D) = k2_xboole_0(k2_tarski(A, B), k2_tarski(C, D)))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', l53_enumset1)).
% 6.00/2.25  tff(f_68, axiom, (![A, B, C, D]: ((D = k1_enumset1(A, B, C)) <=> (![E]: (r2_hidden(E, D) <=> ~((~(E = A) & ~(E = B)) & ~(E = C)))))), file('/export/starexec/sandbox/benchmark/theBenchmark.p', d1_enumset1)).
% 6.00/2.25  tff(c_96, plain, ('#skF_5'!='#skF_8'), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.00/2.25  tff(c_98, plain, ('#skF_7'!='#skF_5'), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.00/2.25  tff(c_70, plain, (![A_43]: (k2_tarski(A_43, A_43)=k1_tarski(A_43))), inference(cnfTransformation, [status(thm)], [f_83])).
% 6.00/2.25  tff(c_74, plain, (![A_46, B_47, C_48]: (k2_enumset1(A_46, A_46, B_47, C_48)=k1_enumset1(A_46, B_47, C_48))), inference(cnfTransformation, [status(thm)], [f_87])).
% 6.00/2.25  tff(c_20, plain, (![A_19]: (k5_xboole_0(A_19, k1_xboole_0)=A_19)), inference(cnfTransformation, [status(thm)], [f_51])).
% 6.00/2.25  tff(c_143, plain, (![A_89, B_90]: (r1_tarski(k3_xboole_0(A_89, B_90), A_89))), inference(cnfTransformation, [status(thm)], [f_35])).
% 6.00/2.25  tff(c_16, plain, (![A_16]: (k1_xboole_0=A_16 | ~r1_tarski(A_16, k1_xboole_0))), inference(cnfTransformation, [status(thm)], [f_47])).
% 6.00/2.25  tff(c_151, plain, (![B_90]: (k3_xboole_0(k1_xboole_0, B_90)=k1_xboole_0)), inference(resolution, [status(thm)], [c_143, c_16])).
% 6.00/2.25  tff(c_427, plain, (![A_120, B_121]: (k5_xboole_0(A_120, k3_xboole_0(A_120, B_121))=k4_xboole_0(A_120, B_121))), inference(cnfTransformation, [status(thm)], [f_33])).
% 6.00/2.25  tff(c_445, plain, (![B_90]: (k5_xboole_0(k1_xboole_0, k1_xboole_0)=k4_xboole_0(k1_xboole_0, B_90))), inference(superposition, [status(thm), theory('equality')], [c_151, c_427])).
% 6.00/2.25  tff(c_453, plain, (![B_122]: (k4_xboole_0(k1_xboole_0, B_122)=k1_xboole_0)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_445])).
% 6.00/2.25  tff(c_22, plain, (![A_20, B_21]: (k5_xboole_0(A_20, k4_xboole_0(B_21, A_20))=k2_xboole_0(A_20, B_21))), inference(cnfTransformation, [status(thm)], [f_53])).
% 6.00/2.25  tff(c_458, plain, (![B_122]: (k5_xboole_0(B_122, k1_xboole_0)=k2_xboole_0(B_122, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_453, c_22])).
% 6.00/2.25  tff(c_523, plain, (![B_126]: (k2_xboole_0(B_126, k1_xboole_0)=B_126)), inference(demodulation, [status(thm), theory('equality')], [c_20, c_458])).
% 6.00/2.25  tff(c_2, plain, (![B_2, A_1]: (k2_xboole_0(B_2, A_1)=k2_xboole_0(A_1, B_2))), inference(cnfTransformation, [status(thm)], [f_27])).
% 6.00/2.25  tff(c_529, plain, (![B_126]: (k2_xboole_0(k1_xboole_0, B_126)=B_126)), inference(superposition, [status(thm), theory('equality')], [c_523, c_2])).
% 6.00/2.25  tff(c_100, plain, (r1_tarski(k2_tarski('#skF_5', '#skF_6'), k2_tarski('#skF_7', '#skF_8'))), inference(cnfTransformation, [status(thm)], [f_122])).
% 6.00/2.25  tff(c_5029, plain, (![B_273, C_274, A_275]: (k2_tarski(B_273, C_274)=A_275 | k1_tarski(C_274)=A_275 | k1_tarski(B_273)=A_275 | k1_xboole_0=A_275 | ~r1_tarski(A_275, k2_tarski(B_273, C_274)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.00/2.25  tff(c_5124, plain, (k2_tarski('#skF_7', '#skF_8')=k2_tarski('#skF_5', '#skF_6') | k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_8') | k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7') | k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(resolution, [status(thm)], [c_100, c_5029])).
% 6.00/2.25  tff(c_5129, plain, (k2_tarski('#skF_5', '#skF_6')=k1_xboole_0), inference(splitLeft, [status(thm)], [c_5124])).
% 6.00/2.25  tff(c_50, plain, (![D_34, A_29]: (r2_hidden(D_34, k2_tarski(A_29, D_34)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.00/2.25  tff(c_5203, plain, (r2_hidden('#skF_6', k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_5129, c_50])).
% 6.00/2.25  tff(c_185, plain, (![B_95, A_96]: (k3_xboole_0(B_95, A_96)=k3_xboole_0(A_96, B_95))), inference(cnfTransformation, [status(thm)], [f_29])).
% 6.00/2.25  tff(c_201, plain, (![B_95]: (k3_xboole_0(B_95, k1_xboole_0)=k1_xboole_0)), inference(superposition, [status(thm), theory('equality')], [c_185, c_151])).
% 6.00/2.25  tff(c_92, plain, (![B_75, C_76]: (r1_tarski(k1_tarski(B_75), k2_tarski(B_75, C_76)))), inference(cnfTransformation, [status(thm)], [f_112])).
% 6.00/2.25  tff(c_387, plain, (![A_116, B_117]: (k3_xboole_0(A_116, B_117)=A_116 | ~r1_tarski(A_116, B_117))), inference(cnfTransformation, [status(thm)], [f_43])).
% 6.00/2.25  tff(c_409, plain, (![B_75, C_76]: (k3_xboole_0(k1_tarski(B_75), k2_tarski(B_75, C_76))=k1_tarski(B_75))), inference(resolution, [status(thm)], [c_92, c_387])).
% 6.00/2.25  tff(c_5182, plain, (k3_xboole_0(k1_tarski('#skF_5'), k1_xboole_0)=k1_tarski('#skF_5')), inference(superposition, [status(thm), theory('equality')], [c_5129, c_409])).
% 6.00/2.25  tff(c_5211, plain, (k1_tarski('#skF_5')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_201, c_5182])).
% 6.00/2.25  tff(c_1213, plain, (![D_158, B_159, A_160]: (D_158=B_159 | D_158=A_160 | ~r2_hidden(D_158, k2_tarski(A_160, B_159)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.00/2.25  tff(c_1222, plain, (![D_158, A_43]: (D_158=A_43 | D_158=A_43 | ~r2_hidden(D_158, k1_tarski(A_43)))), inference(superposition, [status(thm), theory('equality')], [c_70, c_1213])).
% 6.00/2.25  tff(c_5376, plain, (![D_285]: (D_285='#skF_5' | D_285='#skF_5' | ~r2_hidden(D_285, k1_xboole_0))), inference(superposition, [status(thm), theory('equality')], [c_5211, c_1222])).
% 6.00/2.25  tff(c_5387, plain, ('#skF_5'='#skF_6'), inference(resolution, [status(thm)], [c_5203, c_5376])).
% 6.00/2.25  tff(c_5395, plain, (k2_tarski('#skF_6', '#skF_6')=k1_xboole_0), inference(demodulation, [status(thm), theory('equality')], [c_5387, c_5129])).
% 6.00/2.25  tff(c_66, plain, (![A_35, B_36, C_37, D_38]: (k2_xboole_0(k2_tarski(A_35, B_36), k2_tarski(C_37, D_38))=k2_enumset1(A_35, B_36, C_37, D_38))), inference(cnfTransformation, [status(thm)], [f_79])).
% 6.00/2.25  tff(c_5429, plain, (![C_37, D_38]: (k2_xboole_0(k1_xboole_0, k2_tarski(C_37, D_38))=k2_enumset1('#skF_6', '#skF_6', C_37, D_38))), inference(superposition, [status(thm), theory('equality')], [c_5395, c_66])).
% 6.00/2.25  tff(c_5501, plain, (![C_291, D_292]: (k1_enumset1('#skF_6', C_291, D_292)=k2_tarski(C_291, D_292))), inference(demodulation, [status(thm), theory('equality')], [c_74, c_529, c_5429])).
% 6.00/2.25  tff(c_30, plain, (![E_28, B_23, C_24]: (r2_hidden(E_28, k1_enumset1(E_28, B_23, C_24)))), inference(cnfTransformation, [status(thm)], [f_68])).
% 6.00/2.25  tff(c_5559, plain, (![C_293, D_294]: (r2_hidden('#skF_6', k2_tarski(C_293, D_294)))), inference(superposition, [status(thm), theory('equality')], [c_5501, c_30])).
% 6.00/2.25  tff(c_48, plain, (![D_34, B_30, A_29]: (D_34=B_30 | D_34=A_29 | ~r2_hidden(D_34, k2_tarski(A_29, B_30)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.00/2.25  tff(c_5567, plain, (![D_294, C_293]: (D_294='#skF_6' | C_293='#skF_6')), inference(resolution, [status(thm)], [c_5559, c_48])).
% 6.00/2.25  tff(c_5570, plain, (![C_295]: (C_295='#skF_6')), inference(splitLeft, [status(thm)], [c_5567])).
% 6.00/2.25  tff(c_5398, plain, ('#skF_7'!='#skF_6'), inference(demodulation, [status(thm), theory('equality')], [c_5387, c_98])).
% 6.00/2.25  tff(c_5913, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_5570, c_5398])).
% 6.00/2.25  tff(c_5916, plain, (![D_5996]: (D_5996='#skF_6')), inference(splitRight, [status(thm)], [c_5567])).
% 6.00/2.25  tff(c_6261, plain, $false, inference(superposition, [status(thm), theory('equality')], [c_5916, c_5398])).
% 6.00/2.25  tff(c_6262, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7') | k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_8') | k2_tarski('#skF_7', '#skF_8')=k2_tarski('#skF_5', '#skF_6')), inference(splitRight, [status(thm)], [c_5124])).
% 6.00/2.25  tff(c_6265, plain, (k2_tarski('#skF_7', '#skF_8')=k2_tarski('#skF_5', '#skF_6')), inference(splitLeft, [status(thm)], [c_6262])).
% 6.00/2.25  tff(c_6348, plain, (r2_hidden('#skF_8', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6265, c_50])).
% 6.00/2.25  tff(c_6371, plain, ('#skF_6'='#skF_8' | '#skF_5'='#skF_8'), inference(resolution, [status(thm)], [c_6348, c_48])).
% 6.00/2.25  tff(c_6374, plain, ('#skF_6'='#skF_8'), inference(negUnitSimplification, [status(thm)], [c_96, c_6371])).
% 6.00/2.25  tff(c_52, plain, (![D_34, B_30]: (r2_hidden(D_34, k2_tarski(D_34, B_30)))), inference(cnfTransformation, [status(thm)], [f_77])).
% 6.00/2.25  tff(c_6345, plain, (r2_hidden('#skF_7', k2_tarski('#skF_5', '#skF_6'))), inference(superposition, [status(thm), theory('equality')], [c_6265, c_52])).
% 6.00/2.25  tff(c_6357, plain, ('#skF_7'='#skF_6' | '#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_6345, c_48])).
% 6.00/2.25  tff(c_6360, plain, ('#skF_7'='#skF_6'), inference(negUnitSimplification, [status(thm)], [c_98, c_6357])).
% 6.00/2.25  tff(c_6362, plain, (k2_tarski('#skF_5', '#skF_6')=k2_tarski('#skF_6', '#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_6360, c_6265])).
% 6.00/2.25  tff(c_6396, plain, (k2_tarski('#skF_5', '#skF_8')=k1_tarski('#skF_8')), inference(demodulation, [status(thm), theory('equality')], [c_70, c_6374, c_6374, c_6362])).
% 6.00/2.25  tff(c_6449, plain, (r2_hidden('#skF_5', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_6396, c_52])).
% 6.00/2.25  tff(c_6466, plain, ('#skF_5'='#skF_8'), inference(resolution, [status(thm)], [c_6449, c_1222])).
% 6.00/2.25  tff(c_6470, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_96, c_6466])).
% 6.00/2.25  tff(c_6471, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_8') | k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7')), inference(splitRight, [status(thm)], [c_6262])).
% 6.00/2.25  tff(c_6618, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_7')), inference(splitLeft, [status(thm)], [c_6471])).
% 6.00/2.25  tff(c_6688, plain, (r2_hidden('#skF_5', k1_tarski('#skF_7'))), inference(superposition, [status(thm), theory('equality')], [c_6618, c_52])).
% 6.00/2.25  tff(c_6698, plain, ('#skF_7'='#skF_5'), inference(resolution, [status(thm)], [c_6688, c_1222])).
% 6.00/2.25  tff(c_6702, plain, $false, inference(negUnitSimplification, [status(thm)], [c_98, c_98, c_6698])).
% 6.00/2.25  tff(c_6703, plain, (k2_tarski('#skF_5', '#skF_6')=k1_tarski('#skF_8')), inference(splitRight, [status(thm)], [c_6471])).
% 6.00/2.25  tff(c_6774, plain, (r2_hidden('#skF_5', k1_tarski('#skF_8'))), inference(superposition, [status(thm), theory('equality')], [c_6703, c_52])).
% 6.00/2.25  tff(c_6785, plain, ('#skF_5'='#skF_8'), inference(resolution, [status(thm)], [c_6774, c_1222])).
% 6.00/2.25  tff(c_6789, plain, $false, inference(negUnitSimplification, [status(thm)], [c_96, c_96, c_6785])).
% 6.00/2.25  % SZS output end CNFRefutation for /export/starexec/sandbox/benchmark/theBenchmark.p
% 6.00/2.25  
% 6.00/2.25  Inference rules
% 6.00/2.25  ----------------------
% 6.00/2.25  #Ref     : 0
% 6.00/2.25  #Sup     : 1789
% 6.00/2.25  #Fact    : 0
% 6.00/2.25  #Define  : 0
% 6.00/2.25  #Split   : 4
% 6.00/2.25  #Chain   : 0
% 6.00/2.25  #Close   : 0
% 6.00/2.25  
% 6.00/2.25  Ordering : KBO
% 6.00/2.25  
% 6.00/2.25  Simplification rules
% 6.00/2.25  ----------------------
% 6.00/2.25  #Subsume      : 54
% 6.00/2.25  #Demod        : 1533
% 6.00/2.25  #Tautology    : 1140
% 6.00/2.25  #SimpNegUnit  : 5
% 6.00/2.25  #BackRed      : 68
% 6.00/2.25  
% 6.00/2.25  #Partial instantiations: 195
% 6.00/2.25  #Strategies tried      : 1
% 6.00/2.25  
% 6.00/2.25  Timing (in seconds)
% 6.00/2.25  ----------------------
% 6.00/2.25  Preprocessing        : 0.34
% 6.00/2.25  Parsing              : 0.16
% 6.00/2.25  CNF conversion       : 0.03
% 6.00/2.25  Main loop            : 1.08
% 6.00/2.25  Inferencing          : 0.36
% 6.00/2.25  Reduction            : 0.46
% 6.00/2.25  Demodulation         : 0.38
% 6.00/2.25  BG Simplification    : 0.04
% 6.00/2.25  Subsumption          : 0.16
% 6.00/2.25  Abstraction          : 0.05
% 6.00/2.25  MUC search           : 0.00
% 6.00/2.25  Cooper               : 0.00
% 6.00/2.25  Total                : 1.46
% 6.00/2.25  Index Insertion      : 0.00
% 6.00/2.25  Index Deletion       : 0.00
% 6.00/2.25  Index Matching       : 0.00
% 6.00/2.25  BG Taut test         : 0.00
%------------------------------------------------------------------------------
